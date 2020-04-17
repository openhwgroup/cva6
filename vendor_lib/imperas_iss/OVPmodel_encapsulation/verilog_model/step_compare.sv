//
// Copyright 2020 OpenHW Group
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 
//


`ifndef __UVMT_CV32_STEP_COMPARE_SV__
`define __UVMT_CV32_STEP_COMPARE_SV__

// Step-and-Compare between the CV32E40P and Imperas OVPsim ISS
// Cloned from the Imperas demo at $(IMPERAS_HOME)/RTL_OVPmodel_step_compare/verilog_testbench/testbench.sv

/*
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 * Copyright (C) EM Microelectronic US Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.
 *
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

`ifdef COVERAGE
`include "class_coverage.svh" 
`endif

//
// Execute step and compare of dut ISS instance vs riscv RTL instance
//
`ifndef T0_TYPE
  `define T0_TYPE "RV32IMC"
`endif

import params_pkg::*;
import compare_pkg::*;
import uvm_pkg::*;      // needed for the UVM messaging service (`uvm_info(), etc.)


//`define RTL
//`define ISS 

module uvmt_cv32_step_compare
         #(
           parameter int     ROM_START_ADDR = 'h80,//0,      // Must set, no sane default
           parameter int     ROM_BYTE_SIZE  = 4,      // Must be >= 4 for lsu_dp to compile
           parameter int     RAM_BYTE_SIZE  = 4,      // Must be >= 4 for lsu_dp to compile
`ifdef INCISIVE
           parameter         MIF_FILE       = "null"  // Must define, no sane default
`else
           parameter string  MIF_FILE       = "null"  // Must define, no sane default
`endif
          )

          (
           input wire clk_i
          );

    parameter bit COMP_CSR=1; // By default compare CSRs

    // Build the path to the memory init file
    localparam string init_file = {MIF_FILE};
   
/* ISS is in iss_wrap (peer to this module)
    // Instantiate the ISS
    dut #(
        .ID(0), 
        .VENDOR("riscv.ovpworld.org"), 
        .VARIANT(`T0_TYPE), 
        .COMPARE(1)) 
        iss();
*/
   wire   Clk;
   assign Clk = clk_i;
   bit    riscv_core_step;

   // Instantiate interface and bind_pc
   pc_if pc_if_i();
   bind_pc bind_pc_i(pc_if_i);

   initial begin
     string lstr;
     lstr = $sformatf("\tROM_START_ADDR = 0x%0x\n", ROM_START_ADDR);
     lstr = {lstr, $sformatf("\tROM_BYTE_SIZE  = 0x%0x\n", ROM_BYTE_SIZE)};
     lstr = {lstr, $sformatf("\tRAM_BYTE_SIZE  = 0x%0x\n", RAM_BYTE_SIZE)};
     lstr = {lstr, $sformatf("\tinit_file      = %0s\n",   init_file)};
     lstr = {lstr, $sformatf("\tCOMP_CSR       = %0b",     COMP_CSR)};
     `uvm_info ("STEP COMPARE", $sformatf("Parameters:\n%s", lstr), UVM_NONE)

      iss_wrap.cpu.Step = 1;
      riscv_core_step = 1;
      iss_wrap.cpu.StepEnable = 1;
   end
    
   bit ret_iss = 0;
   bit ret_riscv = 0;
   event ev_iss, ev_riscv;
   event compare_ev;
   event advance_clk_ev;

   function void check_32bit(input string compared, input bit [31:0] expected, input logic [31:0] actual);
      if (expected !== actual)
        `uvm_error ("STEP COMPARE", $sformatf("%s expected=0x%8h and actual=0x%8h", compared, expected, actual))
      else
        `uvm_info ("STEP COMPARE", $sformatf("SUCCESS: %s expected=0x%8h==actual", compared, actual), UVM_DEBUG)
   endfunction // check_32bit
   
   
   function automatic void compare();
      int idx;
      logic [31:0][31:0] riscy_GPR; // packed dimensions, register index by data width
      logic [ 5:0] insn_regs_write_addr;
      logic [31:0] insn_regs_write_value;
      int          insn_regs_write_size;
      string       compared_str;

      `uvm_info ("STEP COMPARE", "compare() called", UVM_NONE)

      // Compare PC
      compare_pc(.pc_if_i(pc_if_i));

      // Compare GPR's
      // Assuming that riscv_wrapper_i.riscv_core_i.riscv_tracer_i.insn_regs_write size is never > 1.  Check this.
      insn_regs_write_size = `P2C.riscv_core_i.riscv_tracer_i.insn_regs_write.size();
      if (insn_regs_write_size > 1)
        `uvm_error ("STEP COMPARE", $sformatf("Assume insn_regs_write size is 0 or 1 but is %0d", insn_regs_write_size))
      else if (insn_regs_write_size == 1) begin // Get riscv_wrapper_i.riscv_core_i.riscv_tracer_i.insn_regs_write fields if size is 1
         insn_regs_write_addr = `P2C.riscv_core_i.riscv_tracer_i.insn_regs_write[0].addr;
         insn_regs_write_value = `P2C.riscv_core_i.riscv_tracer_i.insn_regs_write[0].value;
         `uvm_info ("STEP COMPARE", $sformatf("insn_regs_write queue[0] addr=0x%0x, value=0x%0x", insn_regs_write_addr, insn_regs_write_value), UVM_DEBUG)
      end
      
      riscy_GPR = `P2C.riscv_core_i.id_stage_i.registers_i.riscv_register_file_i.mem;

      // Ignore insn_regs_write_addr=0 just like in riscv_tracer.sv
      for (idx=0; idx<32; idx++) begin
         compared_str = $sformatf("GPR[%0d]", idx);
         if ((idx == insn_regs_write_addr) && (idx != 0) && (insn_regs_write_size == 1)) begin// Use register in insn_regs_write queue if it exists
            `uvm_info ("STEP COMPARE", $sformatf("calling check_32bit() using register in insn_regs_write queue"), UVM_DEBUG)
            check_32bit(.compared(compared_str), .expected(iss_wrap.cpu.GPR[idx][31:0]), .actual(insn_regs_write_value));
         end
         else begin // Use actual value from RTL.
            `uvm_info ("STEP COMPARE", $sformatf("calling check_32bit() using actual value from RTL"), UVM_DEBUG)
            check_32bit(.compared(compared_str), .expected(iss_wrap.cpu.GPR[idx][31:0]), .actual(riscy_GPR[idx]));
         end
      end

/*
        // Compare FPR's
        for (idx=0; idx<32; idx++) begin
            if (iss_wrap.cpu.FPR[idx] != t1.cpu.FPR[idx]) begin
                $display("Diff: iss_wrap.F%0d=0x%x", idx, iss_wrap.cpu.FPR[idx]);
                $display("      t1.F%0d=0x%x", idx, t1.cpu.FPR[idx]);
                $display("      iss_wrap.PC=0x%x",   iss_wrap.cpu.PCr);
                $display("      t1.PC=0x%x\n", t1.cpu.PCr);
                $finish;
            end
        end
*/

      // Compare CSR's
      if (COMP_CSR) begin
        bit ignore;
        logic [31:0] csr_val;
        foreach(iss_wrap.cpu.CSR[index]) begin
           ignore = 0;
           csr_val = 0;
           case (index)
             "mstatus": csr_val = {`P2C.riscv_core_i.cs_registers_i.mstatus_q.mprv, // Not documented in Rev 4.3 of user_manual.doc but is in the design
                                   4'b0,
                                   `P2C.riscv_core_i.cs_registers_i.mstatus_q.mpp,
                                   3'b0,
                                   `P2C.riscv_core_i.cs_registers_i.mstatus_q.mpie,
                                   2'b0,
                                   `P2C.riscv_core_i.cs_registers_i.mstatus_q.upie,
                                   `P2C.riscv_core_i.cs_registers_i.mstatus_q.mie,
                                   2'b0,
                                   `P2C.riscv_core_i.cs_registers_i.mstatus_q.uie};
             "misa"    : csr_val = `P2C.riscv_core_i.cs_registers_i.MISA_VALUE;
             "mie"     : csr_val = {`P2C.riscv_core_i.cs_registers_i.mie_q.irq_external,
                                   3'b0,
                                   `P2C.riscv_core_i.cs_registers_i.mie_q.irq_timer,
                                   3'b0,
                                   `P2C.riscv_core_i.cs_registers_i.mie_q.irq_software,
                                   3'b0};
             "miex"    : csr_val = `P2C.riscv_core_i.cs_registers_i.miex_q;
             "mtvec"   : csr_val = {`P2C.riscv_core_i.cs_registers_i.mtvec_q, 6'h0, 2'b01};
             "mtvecx"  : csr_val = {`P2C.riscv_core_i.cs_registers_i.mtvec_q, 6'h0, 2'b01};
             "mscratch": csr_val = `P2C.riscv_core_i.cs_registers_i.mscratch_q;
             "mepc"    : csr_val = `P2C.riscv_core_i.cs_registers_i.mepc_q;
             "mcause"  : csr_val = {`P2C.riscv_core_i.cs_registers_i.mcause_q[6], 
                                    25'b0, 
                                    `P2C.riscv_core_i.cs_registers_i.mcause_q[5:0]};
             "mip"     : csr_val = `P2C.riscv_core_i.cs_registers_i.mip;
             "mipx"    : csr_val = `P2C.riscv_core_i.cs_registers_i.mipx;
             "mhartid" : csr_val = {21'b0, 
                                    `P2C.riscv_core_i.cs_registers_i.cluster_id_i[5:0], 
                                    1'b0, 
                                    `P2C.riscv_core_i.cs_registers_i.core_id_i[3:0]};
             "dcsr"      : csr_val = `P2C.riscv_core_i.cs_registers_i.dcsr_q;     
             "dpc"       : csr_val = `P2C.riscv_core_i.cs_registers_i.depc_q;       
             "dscratch0" : csr_val = `P2C.riscv_core_i.cs_registers_i.dscratch0_q;
             "dscratch1" : csr_val = `P2C.riscv_core_i.cs_registers_i.dscratch1_q;
             "pmpcfg0"   : csr_val = `P2C.riscv_core_i.cs_registers_i.pmp_reg_q.pmpcfg_packed[0];
             "pmpcfg1"   : csr_val = `P2C.riscv_core_i.cs_registers_i.pmp_reg_q.pmpcfg_packed[1];
             "pmpcfg2"   : csr_val = `P2C.riscv_core_i.cs_registers_i.pmp_reg_q.pmpcfg_packed[2];
             "pmpcfg3"   : csr_val = `P2C.riscv_core_i.cs_registers_i.pmp_reg_q.pmpcfg_packed[3];
             "time"   : ignore = 1;
             default: begin
                 $display("%0t: ERROR: index=%s does not match a CSR name", $time, index);
                 ignore = 1;
             end
           endcase // case (index)

           if (!ignore) begin
             `uvm_info ("STEP COMPARE", "Comparing CSRs", UVM_NONE)
             check_32bit(.compared(index), .expected(iss_wrap.cpu.CSR[index]), .actual(csr_val));
           end
        end // foreach (iss_wrap.cpu.CSR[index])
      end // if (COMP_CSR)

       // Compare Vector's ToDo
    endfunction

`ifdef COVERAGE
   coverage cov1;
   initial begin
       cov1 = new();
   end

    function void split(input string in_s, output string s1, s2);
        automatic int i;
        for (i=0; i<in_s.len(); i++) begin
            if (in_s.getc(i) == ":")
                break;
         end
         if (i==0 ) begin
            `uvm_fatal("STEP COMPARE", $sformatf(": not found in split '%0s'", in_s))
         end
         s1 = in_s.substr(0,i-1);
         s2 = in_s.substr(i+1,in_s.len()-1);
    endfunction


    function automatic void sample();
        string decode = iss_wrap.cpu.Decode;
        string ins_str, op[4], key, val;
        int i;
        ins_t ins;
        int num = $sscanf (decode, "%s %s %s %s %s", ins_str, op[0], op[1], op[2], op[3]);
        ins.ins_str = ins_str;
        for (i=0; i<num-1; i++) begin
            split(op[i], key, val);
            ins.ops[i].key=key;
            ins.ops[i].val=val;
        end
        cov1.sample (ins);
    endfunction
`endif


   always @iss_wrap.cpu.Retire begin
      `uvm_info ("STEP COMPARE", "ISS Retired", UVM_NONE)
      iss_wrap.cpu.Step = 0;
      ret_iss = 1;
      ->ev_iss;

`ifdef COVERAGE
      if (iss_wrap.cpu.mode_disass == 1) begin
          sample();
      end
`endif

   end

// riscv_core
   always @(`P2C.riscv_core_i.riscv_tracer_i.retire) begin
      `uvm_info ("STEP COMPARE", "DUT Retired", UVM_DEBUG)
      riscv_core_step = 0;
      ret_riscv=1;
      ->ev_riscv;
   end     
   
    always @(ev_iss or ev_riscv) begin
        if (ret_iss && ret_riscv) begin
           fork
             begin: waiting
               iss_wrap.cpu.busWait();
               disable delaying;
               `uvm_info ("STEP COMPARE", "busWait actually returned", UVM_DEBUG)
             end

             begin: delaying
               //#60ns;
               repeat(3) @(posedge Clk);
               disable waiting;
               `uvm_info ("STEP COMPARE", "busWait never returned", UVM_DEBUG)
               ->advance_clk_ev;
               riscv_core_step = 1;
               repeat(2) @(posedge Clk);
             end
           join_any;
           compare();
           ret_iss = 0;
           ret_riscv = 0;
           iss_wrap.cpu.Step = 1;
           riscv_core_step = 1;
           ->compare_ev;
        end
    end

/* Does this module even need a clock?!?
   // Run riscv_core.Clk if riscv_core_step=1
   initial begin
      forever begin
         #2ns; // For riscv_core_step to update
         if (riscv_core_step) begin
            #8ns Clk <= !Clk;
            #10ns Clk <= !Clk; // Keep period at 20ns
            end
         else
           @(compare_ev);
      end
   end
*/

/* CV32E40P (RISCY) is in dut_wrap (peer to this module)
   // RISCY inputs
   bit rst_ni;
   bit clock_en_i;    // enable clock, otherwise it is gated
   bit test_en_i;     // enable all clock gates for testing
   bit fregfile_disable_i;  // disable the fp regfile, using int regfile instead
   bit debug_req_i; // Debug Interface
   bit fetch_enable_i; // CPU Control Signal
   // Core ID, Cluster ID and boot address are considered more or less static
   bit [ 3:0] core_id_i;
   bit [ 5:0] cluster_id_i;

   // RISCY outputs. NOTE: Some outputs are captured by the interfaces declared later.
   logic      core_busy_o; // CPU Control Signal
   logic [N_EXT_PERF_COUNTERS-1:0] ext_perf_counters_i;

   initial begin
      rst_ni = 0;
      clock_en_i = 1;
      test_en_i = 0; 
      fregfile_disable_i = 0;
      debug_req_i = 0;
      fetch_enable_i = 1;
      core_id_i = 0;
      cluster_id_i = 0;

      repeat (2) @(negedge Clk);
      rst_ni = 1; // Deassert reset
   end
   
   // Instantiate the interfaces
   irq_if irq_bus(Clk, rst_ni);
   mem_if instr_mem_bus(Clk, rst_ni);
   mem_if data_mem_bus(Clk, rst_ni);
   apu_ic_if apu_ic_bus(Clk, rst_ni);
 
   // Instantiate LSU dual port for ROM and RAM
   // Directions relative to RISCY
   lsu_dp #(.ROM_START_ADDR(ROM_START_ADDR),
            .ROM_MEM_DEPTH(ROM_BYTE_SIZE/4),
            .RAM_MEM_DEPTH(RAM_BYTE_SIZE/4),
            .init_file(init_file)) 
   lsu_dp(
          .clk_i(Clk), 
          .rst_ni(rst_ni),
          .req_instr(instr_mem_bus.req_o),   
          .gnt_instr(instr_mem_bus.gnt_i),   
          .rvalid_instr(instr_mem_bus.rvalid_i),
          .we_instr(1'b0), // no write on instruciton bus since no stores
          .be_instr({4{1'bx}}), // ignored
          .addr_instr(instr_mem_bus.addr_o-ROM_START_ADDR),
          .wdata_instr({32{1'bx}}), // ignored
          .rdata_instr(instr_mem_bus.rdata_i),

          .req_data(data_mem_bus.req_o),   
          .gnt_data(data_mem_bus.gnt_i),   
          .rvalid_data(data_mem_bus.rvalid_i),
          .we_data(data_mem_bus.we_o),
          .be_data(data_mem_bus.be_o),
          .addr_data(data_mem_bus.addr_o-ROM_START_ADDR),
          .wdata_data(data_mem_bus.wdata_o),
          .rdata_data(data_mem_bus.rdata_i)
          );             

   // Instantiate the DUT
   riscv_core #(
                .N_EXT_PERF_COUNTERS(N_EXT_PERF_COUNTERS),
                .INSTR_RDATA_WIDTH  (INSTR_RDATA_WIDTH),
                .PULP_SECURE        ( 1),
                .N_PMP_ENTRIES      (16),
                .USE_PMP            ( 1),
                .PULP_CLUSTER       ( 0),
                .A_EXTENSION        ( 0),
                .FPU                ( 0),
                .FP_DIVSQRT         ( 0),
                .SHARED_FP          ( 0),
                .SHARED_DSP_MULT    ( 0),
                .SHARED_INT_DIV     ( 0),
                .SHARED_FP_DIVSQRT  ( 0),
                .WAPUTYPE           (WAPUTYPE),
                .APU_NARGS_CPU      (APU_NARGS_CPU),
                .APU_WOP_CPU        (APU_WOP_CPU),
                .APU_NDSFLAGS_CPU   (APU_NDSFLAGS_CPU),
                .APU_NUSFLAGS_CPU   (APU_NUSFLAGS_CPU),
                .DM_HaltAddress     (32'h0001_5000 + 32'h800))
   riscv_core(
              // Clock and Reset
              .clk_i(Clk), // Input
              .rst_ni(rst_ni), // Input
              .clock_en_i(clock_en_i), // Input
              .test_en_i(test_en_i), // Input 
              .fregfile_disable_i(fregfile_disable_i), // Input
              // Core ID, Cluster ID and boot address are considered more or less static
              .boot_addr_i(ROM_START_ADDR), // Input
              .core_id_i(core_id_i), // Input
              .cluster_id_i(cluster_id_i), // Input

              // Instruction memory interface
              .instr_req_o(instr_mem_bus.req_o),  // Output
              .instr_gnt_i(instr_mem_bus.gnt_i), // Input
              .instr_rvalid_i(instr_mem_bus.rvalid_i), // Input
              .instr_addr_o(instr_mem_bus.addr_o), // Output
              .instr_rdata_i(instr_mem_bus.rdata_i), // Input

              // Data memory interface
              .data_req_o(data_mem_bus.req_o),
              .data_gnt_i(data_mem_bus.gnt_i),
              .data_rvalid_i(data_mem_bus.rvalid_i),
              .data_we_o(data_mem_bus.we_o),
              .data_be_o(data_mem_bus.be_o),
              .data_addr_o(data_mem_bus.addr_o),
              .data_wdata_o(data_mem_bus.wdata_o),
              .data_rdata_i(data_mem_bus.rdata_i),

              .data_atop_o(), // atomic operation, only active if parameter `A_EXTENSION != 0`
 

              // apu-interconnect
              // handshake signals
              .apu_master_req_o(apu_ic_bus.apu_master_req_o),
              .apu_master_ready_o(apu_ic_bus.apu_master_ready_o),
              .apu_master_gnt_i(apu_ic_bus.apu_master_gnt_i),
              // request channel
              .apu_master_operands_o(apu_ic_bus.apu_master_operands_o),
              .apu_master_op_o(apu_ic_bus.apu_master_op_o),
              .apu_master_type_o(apu_ic_bus.apu_master_type_o),
              .apu_master_flags_o(apu_ic_bus.apu_master_flags_o),
              // response channel
              .apu_master_valid_i(apu_ic_bus.apu_master_valid_i),
              .apu_master_result_i(apu_ic_bus.apu_master_result_i),
              .apu_master_flags_i(apu_ic_bus.apu_master_flags_i),

              // Interrupt inputs
              .irq_sec_i(irq_bus.irq_sec_i),
              .irq_software_i(irq_bus.irq_software_i),
              .irq_timer_i(irq_bus.irq_timer_i),
              .irq_external_i(irq_bus.irq_external_i),
              .irq_fast_i(irq_bus.irq_fast_i),
              .irq_nmi_i(irq_bus.irq_nmi_i),
              .irq_fastx_i(irq_bus.irq_fastx_i),
              // Interrupt puts
              .irq_ack_o(irq_bus.irq_ack_o),
              .irq_id_o(irq_bus.irq_id_o),
              .sec_lvl_o(irq_bus.sec_lvl_o),

              // Debug Interface
              .debug_req_i(debug_req_i),
              // CPU Control Signals
              .fetch_enable_i(fetch_enable_i),
              .core_busy_o(core_busy_o),
              
              .ext_perf_counters_i(ext_perf_counters_i)
              );
*/

endmodule: uvmt_cv32_step_compare

`endif //__UVMT_CV32_STEP_COMPARE_SV__
