// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// Instruction tracer for CVA6. Samples the RVFI interface at commit and hands
// every retirement to a DPI-C backend (cva6tb_tracer.cc), which disassembles it
// and writes it out in one of the formats of rv_format.h.
//
// This module contains no strings, classes or queues, so it elaborates equally
// well under Verilator and under event driven simulators.
//
// Plusargs:
//   +notrace                    disable tracing entirely
//   +trace_file=<path>          output file  (default cva6tb_trace_hart_<id>.trace,
//                               .bin for the binary format, .txt for the others)
//   +trace_verbose=<n>          detail level, 0 to 2                       (default 0)
//   +trace_format=<name>        trace, legacy, spike, rvfi or binary   (default trace)
//   +trace_stats=<path>         write an end of run summary here     (default: none)
//   +trace_start=<trigger>      open the trace window   (default: open from the start)
//   +trace_stop=<trigger>       close it                     (default: never closes)
//   +trace_symbols=<elf>[,...]  annotate with symbol names       (default: no names)
//   +trace_symbol_mode=<mode>   header, inline or both                (default header)
//   +trace_symbol_start=<trig>  open the annotation window
//   +trace_symbol_stop=<trig>   close it
//
// A trigger is a cycle count, `cycle:<n>`, `pc:<hex>` or `sym:<name>`; a symbol
// source is an ELF path, optionally `<path>@<bias>` when the image was placed
// somewhere other than its link address. See rv_trigger.h and rv_symbols.h.

module cva6tb_tracer #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type                   rvfi_instr_t = logic,
    parameter type                   rvfi_csr_t = logic,
    parameter int unsigned           HartId = 0
) (
    input logic                                    clk_i,
    input logic                                    rst_ni,
    input rvfi_instr_t [CVA6Cfg.NrCommitPorts-1:0] rvfi_i,
    // CSR state as cva6_rvfi reports it: per register the current value and
    // whether it changed in this cycle.
    input rvfi_csr_t                               rvfi_csr_i,
    // Trap value of the instruction that traps this cycle. RVFI itself does not
    // carry tval; cva6_rvfi exposes it on rvfi_to_iti_o.tval, registered in the
    // same cycle as the RVFI outputs. Tie to '0 if not available.
    input logic [           CVA6Cfg.XLEN-1:0]      trap_tval_i,
    // Branch resolution, likewise not part of RVFI and likewise taken from
    // rvfi_to_iti_o. Tie both to '0 if not available: the mispredict column
    // then reads 0 everywhere, as it did before the probe existed.
    input logic [CVA6Cfg.NrCommitPorts-1:0]        branch_valid_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0]        branch_taken_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0]        branch_mispredict_i
);

  // The legacy tracer stamped its lines in nanoseconds. Declaring a timeunit
  // here would make every module without one warn, so instead the time literal
  // is resolved into the surrounding time unit and used as a divisor.
  localparam longint unsigned TimeUnitsPerNs = longint'(1ns);

  import "DPI-C" function int cva6tb_tracer_open(
    input string filename,
    input int    xlen,
    input int    vlen,
    input int    plen,
    input int    verbosity,
    input int    extensions
  );

  import "DPI-C" function void cva6tb_tracer_retire(
    input int               handle,
    input longint unsigned  cycle,
    input longint unsigned  sim_time_ns,
    input byte unsigned     commit_port,
    input longint unsigned  order,
    input byte unsigned     priv,
    input byte unsigned     flags,
    input longint unsigned  pc,
    input int unsigned      insn,
    input byte unsigned     rd_addr,
    input longint unsigned  rd_wdata,
    input byte unsigned     rs1_addr,
    input longint unsigned  rs1_rdata,
    input byte unsigned     rs2_addr,
    input longint unsigned  rs2_rdata,
    input longint unsigned  mem_vaddr,
    input longint unsigned  mem_paddr,
    input int unsigned      mem_rmask,
    input int unsigned      mem_wmask,
    input longint unsigned  mem_wdata,
    input longint unsigned  mem_rdata
  );

  import "DPI-C" function void cva6tb_tracer_trap(
    input int              handle,
    input longint unsigned cycle,
    input longint unsigned sim_time_ns,
    input byte unsigned    priv,
    input byte unsigned    virt,
    input longint unsigned pc,
    input int unsigned     insn,
    input longint unsigned cause,
    input longint unsigned tval,
    input byte unsigned    is_interrupt
  );

  import "DPI-C" function void cva6tb_tracer_csr(
    input int                handle,
    input longint unsigned   cycle,
    input longint unsigned   sim_time_ns,
    input shortint unsigned  addr,
    input longint unsigned   value,
    input byte unsigned      initial_value
  );

  import "DPI-C" function int cva6tb_tracer_config(
    input int    handle,
    input string key,
    input string value
  );

  import "DPI-C" function void cva6tb_tracer_close(input int handle);

  // -1 marks "tracing disabled": every backend call then returns immediately
  int                  handle = -1;
  int                  verbosity = 0;
  longint unsigned     cycle = 0;
  longint unsigned     order = 0;

  // Forwards one option to the backend, which owns all of the optional
  // behaviour. A rejected value is a configuration mistake that would otherwise
  // silently produce the wrong trace, so it stops the simulation.
  function automatic void set_option(string key, string value);
    if (cva6tb_tracer_config(handle, key, value) != 0)
      $fatal(1, "[cva6tb_tracer] bad value '%s' for option '%s'", value, key);
  endfunction

  initial begin : open_trace
    string fname;
    string val;
    string ext;
    if (!$test$plusargs("notrace")) begin
      if (!$value$plusargs("trace_file=%s", fname)) begin
        if (!$value$plusargs("trace_format=%s", val)) val = "trace";
        if (val == "trace") ext = "trace";
        else if (val == "binary") ext = "bin";
        else ext = "txt";
        fname = $sformatf("cva6tb_trace_hart_%0d.%s", HartId, ext);
      end
      if (!$value$plusargs("trace_verbose=%d", verbosity)) verbosity = 0;
      // bit 0 marks Zcmt, whose cm.jt/cm.jalt share the c.fsdsp encoding
      handle = cva6tb_tracer_open(fname, CVA6Cfg.XLEN, CVA6Cfg.VLEN, CVA6Cfg.PLEN, verbosity,
                                  CVA6Cfg.RVZCMT ? 32'h1 : 32'h0);

      // Everything optional is forwarded by name. Adding an option later means
      // one more row here and one more key in the backend. Symbols are loaded
      // first so that triggers can name them.
      if (handle >= 0) begin
        set_option("hart_id", $sformatf("%0d", HartId));
        if ($value$plusargs("trace_format=%s", val)) set_option("format", val);
        if ($value$plusargs("trace_stats=%s", val)) set_option("stats", val);
        if ($value$plusargs("trace_symbols=%s", val)) set_option("symbols", val);
        if ($value$plusargs("trace_symbol_mode=%s", val)) set_option("symbol_mode", val);
        if ($value$plusargs("trace_start=%s", val)) set_option("start", val);
        if ($value$plusargs("trace_stop=%s", val)) set_option("stop", val);
        if ($value$plusargs("trace_symbol_start=%s", val)) set_option("symbol_start", val);
        if ($value$plusargs("trace_symbol_stop=%s", val)) set_option("symbol_stop", val);
      end
    end
  end

  // Hands one CSR to the backend: every CSR once at the first cycle, to give it
  // a copy of the state, and from then on each one whose value changed.
  bit csrs_sent = 1'b0;

`define CVA6TB_TRACER_CSR(ADDR, FIELD) \
    if (rvfi_csr_i.FIELD.rmask != 0 && (!csrs_sent || rvfi_csr_i.FIELD.wmask != 0)) \
      cva6tb_tracer_csr(handle, cycle, $time / TimeUnitsPerNs, ADDR, \
                        64'(rvfi_csr_i.FIELD.wdata), byte'(!csrs_sent));

  task automatic send_csrs();
    `CVA6TB_TRACER_CSR(12'h001, fflags)
    `CVA6TB_TRACER_CSR(12'h002, frm)
    `CVA6TB_TRACER_CSR(12'h003, fcsr)
    `CVA6TB_TRACER_CSR(12'h017, jvt)
    `CVA6TB_TRACER_CSR(12'h800, ftran)
    `CVA6TB_TRACER_CSR(12'h7B0, dcsr)
    `CVA6TB_TRACER_CSR(12'h7B1, dpc)
    `CVA6TB_TRACER_CSR(12'h7B2, dscratch0)
    `CVA6TB_TRACER_CSR(12'h7B3, dscratch1)
    `CVA6TB_TRACER_CSR(12'h100, sstatus)
    `CVA6TB_TRACER_CSR(12'h104, sie)
    `CVA6TB_TRACER_CSR(12'h144, sip)
    `CVA6TB_TRACER_CSR(12'h105, stvec)
    `CVA6TB_TRACER_CSR(12'h106, scounteren)
    `CVA6TB_TRACER_CSR(12'h140, sscratch)
    `CVA6TB_TRACER_CSR(12'h141, sepc)
    `CVA6TB_TRACER_CSR(12'h142, scause)
    `CVA6TB_TRACER_CSR(12'h143, stval)
    `CVA6TB_TRACER_CSR(12'h180, satp)
    `CVA6TB_TRACER_CSR(12'h300, mstatus)
    `CVA6TB_TRACER_CSR(12'h310, mstatush)
    `CVA6TB_TRACER_CSR(12'h301, misa)
    `CVA6TB_TRACER_CSR(12'h302, medeleg)
    `CVA6TB_TRACER_CSR(12'h303, mideleg)
    `CVA6TB_TRACER_CSR(12'h304, mie)
    `CVA6TB_TRACER_CSR(12'h305, mtvec)
    `CVA6TB_TRACER_CSR(12'h306, mcounteren)
    `CVA6TB_TRACER_CSR(12'h340, mscratch)
    `CVA6TB_TRACER_CSR(12'h341, mepc)
    `CVA6TB_TRACER_CSR(12'h342, mcause)
    `CVA6TB_TRACER_CSR(12'h343, mtval)
    `CVA6TB_TRACER_CSR(12'h344, mip)
    `CVA6TB_TRACER_CSR(12'h30A, menvcfg)
    `CVA6TB_TRACER_CSR(12'h31A, menvcfgh)
    `CVA6TB_TRACER_CSR(12'hF11, mvendorid)
    `CVA6TB_TRACER_CSR(12'hF12, marchid)
    `CVA6TB_TRACER_CSR(12'hF14, mhartid)
    `CVA6TB_TRACER_CSR(12'h320, mcountinhibit)
    `CVA6TB_TRACER_CSR(12'hB00, mcycle)
    `CVA6TB_TRACER_CSR(12'hB80, mcycleh)
    `CVA6TB_TRACER_CSR(12'hB02, minstret)
    `CVA6TB_TRACER_CSR(12'hB82, minstreth)
    `CVA6TB_TRACER_CSR(12'hC00, cycle)
    `CVA6TB_TRACER_CSR(12'hC80, cycleh)
    `CVA6TB_TRACER_CSR(12'hC02, instret)
    `CVA6TB_TRACER_CSR(12'hC82, instreth)
    `CVA6TB_TRACER_CSR(12'h7C1, dcache)
    `CVA6TB_TRACER_CSR(12'h7C0, icache)
    `CVA6TB_TRACER_CSR(12'h7C2, acc_cons)
    `CVA6TB_TRACER_CSR(12'h3A0, pmpcfg0)
    `CVA6TB_TRACER_CSR(12'h3A1, pmpcfg1)
    `CVA6TB_TRACER_CSR(12'h3A2, pmpcfg2)
    `CVA6TB_TRACER_CSR(12'h3A3, pmpcfg3)
    for (int unsigned j = 0; j < 16; j++) begin
      `CVA6TB_TRACER_CSR(12'(12'h3B0 + j), pmpaddr[j])
    end
    `CVA6TB_TRACER_CSR(12'h600, hstatus)
    `CVA6TB_TRACER_CSR(12'h602, hedeleg)
    `CVA6TB_TRACER_CSR(12'h603, hideleg)
    `CVA6TB_TRACER_CSR(12'h606, hcounteren)
    `CVA6TB_TRACER_CSR(12'h607, hgeie)
    `CVA6TB_TRACER_CSR(12'h643, htval)
    `CVA6TB_TRACER_CSR(12'h64A, htinst)
    `CVA6TB_TRACER_CSR(12'h680, hgatp)
    `CVA6TB_TRACER_CSR(12'h200, vsstatus)
    `CVA6TB_TRACER_CSR(12'h205, vstvec)
    `CVA6TB_TRACER_CSR(12'h240, vsscratch)
    `CVA6TB_TRACER_CSR(12'h241, vsepc)
    `CVA6TB_TRACER_CSR(12'h242, vscause)
    `CVA6TB_TRACER_CSR(12'h243, vstval)
    `CVA6TB_TRACER_CSR(12'h280, vsatp)
    `CVA6TB_TRACER_CSR(12'h34A, mtinst)
    `CVA6TB_TRACER_CSR(12'h34B, mtval2)
    `CVA6TB_TRACER_CSR(12'h307, mtvt)
    `CVA6TB_TRACER_CSR(12'h346, mintstatus)
    `CVA6TB_TRACER_CSR(12'h347, mintthresh)
    `CVA6TB_TRACER_CSR(12'h107, stvt)
    `CVA6TB_TRACER_CSR(12'h147, sintthresh)
    `CVA6TB_TRACER_CSR(12'h207, vstvt)
    `CVA6TB_TRACER_CSR(12'h247, vsintthresh)
    csrs_sent = 1'b1;
  endtask

`undef CVA6TB_TRACER_CSR

  // bookkeeping is testbench local state, so plain blocking updates are used
  always @(posedge clk_i) begin : trace
    byte unsigned flags;
    if (!rst_ni) begin
      cycle = 0;
    end else begin
      cycle = cycle + 1;
      if (handle >= 0) begin
        // CSR changes first, so that the backend can attach them to the
        // instruction or trap of this cycle that made them
        send_csrs();
        for (int unsigned i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
          if (rvfi_i[i].valid) begin
            flags = 8'b0;
            if (branch_mispredict_i[i]) flags[0] = 1'b1;
            if (rvfi_i[i].intr[0]) flags[1] = 1'b1;
            if (rvfi_i[i].intr[2]) flags[2] = 1'b1;
            if (branch_valid_i[i]) flags[3] = 1'b1;
            if (branch_taken_i[i]) flags[4] = 1'b1;
            if (rvfi_i[i].virt[0]) flags[5] = 1'b1;
            cva6tb_tracer_retire(
                handle,
                cycle,
                $time / TimeUnitsPerNs,
                8'(i),
                order,
                8'(rvfi_i[i].mode),
                flags,
                64'(rvfi_i[i].pc_rdata[CVA6Cfg.VLEN-1:0]),
                32'(rvfi_i[i].insn),
                8'(rvfi_i[i].rd_addr),
                64'(rvfi_i[i].rd_wdata),
                8'(rvfi_i[i].rs1_addr),
                64'(rvfi_i[i].rs1_rdata),
                8'(rvfi_i[i].rs2_addr),
                64'(rvfi_i[i].rs2_rdata),
                64'(rvfi_i[i].mem_addr),
                64'(rvfi_i[i].mem_paddr),
                32'(rvfi_i[i].mem_rmask),
                32'(rvfi_i[i].mem_wmask),
                64'(rvfi_i[i].mem_wdata),
                64'(rvfi_i[i].mem_rdata)
            );
            order = order + 1;
          end else if (rvfi_i[i].trap) begin
            cva6tb_tracer_trap(
                handle,
                cycle,
                $time / TimeUnitsPerNs,
                8'(rvfi_i[i].mode),
                8'(rvfi_i[i].virt),
                64'(rvfi_i[i].pc_rdata[CVA6Cfg.VLEN-1:0]),
                32'(rvfi_i[i].insn),
                64'(rvfi_i[i].cause),
                64'(trap_tval_i),
                8'(rvfi_i[i].cause[CVA6Cfg.XLEN-1])
            );
          end
        end
      end
    end
  end

  final cva6tb_tracer_close(handle);

endmodule
