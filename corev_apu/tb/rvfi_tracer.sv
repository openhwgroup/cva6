// Copyright 2020 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON (jean-roch.coulon@invia.fr)

module rvfi_tracer #(
  parameter logic [7:0] HART_ID      = '0,
  parameter int unsigned DEBUG_START = 0,
  parameter int unsigned NR_COMMIT_PORTS = 2,
  parameter int unsigned DEBUG_STOP  = 0
)(
  input logic                           clk_i,
  input logic                           rst_ni,
  input rvfi_pkg::rvfi_instr_t[NR_COMMIT_PORTS-1:0]           rvfi_i
);

  int f;
  int unsigned SIM_FINISH;
  initial begin
    f = $fopen($sformatf("trace_rvfi_hart_%h.dasm", HART_ID), "w");
    if (!$value$plusargs("time_out=%d", SIM_FINISH)) SIM_FINISH = 2000000;
  end

  final $fclose(f);

  logic [31:0] cycles;
  // Generate the trace based on RVFI
  logic [63:0] pc64;
  string cause;
  always_ff @(posedge clk_i) begin
    for (int i = 0; i < NR_COMMIT_PORTS; i++) begin
      pc64 = {{riscv::XLEN-riscv::VLEN{rvfi_i[i].pc_rdata[riscv::VLEN-1]}}, rvfi_i[i].pc_rdata};
      // print the instruction information if the instruction is valid or a trap is taken
      if (rvfi_i[i].valid) begin
        // Instruction information
        $fwrite(f, "core   0: 0x%h (0x%h) DASM(%h)\n",
          pc64, rvfi_i[i].insn, rvfi_i[i].insn);
        // Destination register information
        if (rvfi_i[i].insn[1:0] != 2'b11) begin
          $fwrite(f, "%h 0x%h (0x%h)",
            rvfi_i[i].mode, pc64, rvfi_i[i].insn[15:0]);
        end else begin
          $fwrite(f, "%h 0x%h (0x%h)",
            rvfi_i[i].mode, pc64, rvfi_i[i].insn);
        end
        // Decode instruction to know if destination register is FP register.
        // Handle both uncompressed and compressed instructions.
        if ( rvfi_i[i].insn[6:0] == 7'b1001111 ||
             rvfi_i[i].insn[6:0] == 7'b1001011 ||
             rvfi_i[i].insn[6:0] == 7'b1000111 ||
             rvfi_i[i].insn[6:0] == 7'b1000011 ||
             rvfi_i[i].insn[6:0] == 7'b0000111 ||
            (rvfi_i[i].insn[6:0] == 7'b1010011 && rvfi_i[i].insn[31:26] != 6'b111000
                                               && rvfi_i[i].insn[31:26] != 6'b101000
                                               && rvfi_i[i].insn[31:26] != 6'b110000) ||
            (rvfi_i[i].insn[0] == 1'b0 && ((rvfi_i[i].insn[15:13] == 3'b001 && riscv::XLEN == 64) ||
                                           (rvfi_i[i].insn[15:13] == 3'b011 && riscv::XLEN == 32) ))) begin
          $fwrite(f, " f%d 0x%h", rvfi_i[i].rd_addr, rvfi_i[i].rd_wdata);
        end else if (rvfi_i[i].rd_addr != 0) begin
          $fwrite(f, " x%d 0x%h", rvfi_i[i].rd_addr, rvfi_i[i].rd_wdata);
          if (rvfi_i[i].mem_rmask != 0) begin
            $fwrite(f, " mem 0x%h", rvfi_i[i].mem_addr);
          end
        end else begin
          if (rvfi_i[i].mem_wmask != 0) begin
            $fwrite(f, " mem 0x%h 0x%h", rvfi_i[i].mem_addr, rvfi_i[i].mem_wdata);
          end
        end
        $fwrite(f, "\n");
        if (rvfi_i[i].insn == 32'h00000073) begin
          $finish(1);
          $finish(1);
        end
      end else begin
        if (rvfi_i[i].trap) begin
          case (rvfi_i[i].cause)
            32'h0: cause = "INSTR_ADDR_MISALIGNED";
            32'h1: cause = "INSTR_ACCESS_FAULT";
            32'h2: cause = "ILLEGAL_INSTR";
            32'h3: cause = "BREAKPOINT";
            32'h4: cause = "LD_ADDR_MISALIGNED";
            32'h5: cause = "LD_ACCESS_FAULT";
            32'h6: cause = "ST_ADDR_MISALIGNED";
            32'h7: cause = "ST_ACCESS_FAULT";
          endcase;
          $fwrite(f, "%s exception @ 0x%h\n", cause, pc64);
        end
      end
    end
    if (cycles > SIM_FINISH) $finish(1);
  end

  always_ff @(posedge clk_i or negedge rst_ni)
    if (~rst_ni)
      cycles <= 0;
    else
      cycles <= cycles+1;

  // Trace any custom signals
  // Define signals to be traced by adding them into debug and name arrays
  string name[0:10];
  logic[63:0] debug[0:10], debug_previous[0:10];

  always_ff @(posedge clk_i) begin
    if (cycles > DEBUG_START && cycles < DEBUG_STOP)
      for (int index = 0; index < 100; index++)
        if (debug_previous[index] != debug[index])
          $fwrite(f, "%d %s %x\n", cycles, name[index], debug[index]);
    debug_previous <= debug;
  end

endmodule // rvfi_tracer
