// Copyright 2020 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON (jean-roch.coulon@invia.fr)

module rvfi_tracer import ariane_pkg::*; #(
  parameter int unsigned SIM_FINISH  = 1000000,
  parameter logic [7:0] HART_ID      = '0,
  parameter int unsigned DEBUG_START = 0,
  parameter int unsigned DEBUG_STOP  = 0
)(
  input logic                           clk_i,
  input logic                           rst_ni,
  input rvfi_pkg::rvfi_port_t           rvfi_i
);

  int f;
  initial f = $fopen($sformatf("trace_rvfi_hart_%h.dasm", HART_ID), "w");
  final $fclose(f);

  logic [31:0] cycles;
  // Generate the trace based on RVFI
  logic [63:0] pc64;
  always_ff @(posedge clk_i) begin
    for (int i = 0; i < NR_COMMIT_PORTS; i++) begin
      pc64 = {{riscv::XLEN-riscv::VLEN{rvfi_i[i].pc_rdata[riscv::VLEN-1]}}, rvfi_i[i].pc_rdata};
      // print the instruction information if the instruction is valid or a trap is taken
      if (rvfi_i[i].valid) begin
        // Instruction information
        $fwrite(f, "core   0: 0x%h (0x%h) DASM(%h)\n",
          pc64, rvfi_i[i].insn, rvfi_i[i].insn);
        // Destination register information
        $fwrite(f, "%h 0x%h (0x%h)",
          rvfi_i[i].mode, pc64, rvfi_i[i].insn);
        // Decode instruction to know if destination register is FP register
        if ( rvfi_i[i].insn[6:0] == 7'b1001111 ||
             rvfi_i[i].insn[6:0] == 7'b1001011 ||
             rvfi_i[i].insn[6:0] == 7'b1000111 ||
             rvfi_i[i].insn[6:0] == 7'b1000011 ||
             rvfi_i[i].insn[6:0] == 7'b0000111 ||
            (rvfi_i[i].insn[6:0] == 7'b1010011 && rvfi_i[i].insn[31:26] != 6'b111000
                                               && rvfi_i[i].insn[31:26] != 6'b101000
                                               && rvfi_i[i].insn[31:26] != 6'b110000) )
          $fwrite(f, " f%d 0x%h\n",
            rvfi_i[i].rd_addr, rvfi_i[i].rd_wdata);
        else if (rvfi_i[i].rd_addr != 0) begin
          $fwrite(f, " x%d 0x%h\n",
            rvfi_i[i].rd_addr, rvfi_i[i].rd_wdata);
        end else $fwrite(f, "\n");
        if (rvfi_i[i].insn == 32'h00000073) begin
          $finish(1);
          $finish(1);
        end
      end else if (rvfi_i[i].trap)
        $fwrite(f, "exception : 0x%h\n", pc64);
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
