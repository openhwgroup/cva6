// Copyright 2020 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Original Author: Jean-Roch COULON (jean-roch.coulon@invia.fr)

import ariane_pkg::*;

module rvfi_tracer #(
  parameter int unsigned SIM_FINISH = 1000000,
  parameter int unsigned DEBUG_START = 0,
  parameter int unsigned DEBUG_STOP  = 0
)(
  input logic [31:0]                    cycles,
  input rvfi_tracer_pkg::rvfi_port_t    rvfi_i
);

  int f;
  initial f = $fopen("trace_ip.dasm", "w");
  final $fclose(f);

  //Generate the trace based on RVFI
  logic [63:0] pc64;
  always_ff @(posedge i_ariane.clk_i) begin
    for (int i = 0; i < NR_COMMIT_PORTS; i++) begin
      pc64 = {{riscv::XLEN-riscv::VLEN{rvfi_i[i].rvfi_pc_rdata[riscv::VLEN-1]}}, rvfi_i[i].rvfi_pc_rdata};
      //print instruction information if is valid or is trapped
      if (rvfi_i[i].rvfi_valid) begin
        //Instruction information
        $fwrite(f, "core   0: 0x%h (0x%h) DASM(%h)\n",
          pc64, rvfi_i[i].rvfi_insn, rvfi_i[i].rvfi_insn);
        //Destination register information
        $fwrite(f, "%h 0x%h (0x%h)",
          rvfi_i[i].rvfi_mode, pc64, rvfi_i[i].rvfi_insn);
        //Decode instruction to know if destination register is FP register
        if ( rvfi_i[i].rvfi_insn[6:0] == 7'b1001111 ||
             rvfi_i[i].rvfi_insn[6:0] == 7'b1001011 ||
             rvfi_i[i].rvfi_insn[6:0] == 7'b1000111 ||
             rvfi_i[i].rvfi_insn[6:0] == 7'b1000011 ||
             rvfi_i[i].rvfi_insn[6:0] == 7'b0000111 ||
            (rvfi_i[i].rvfi_insn[6:0] == 7'b1010011
                        && rvfi_i[i].rvfi_insn[31:26] != 6'b111000
                        && rvfi_i[i].rvfi_insn[31:26] != 6'b101000
                        && rvfi_i[i].rvfi_insn[31:26] != 6'b110000) )
          $fwrite(f, " f%d 0x%h\n",
            rvfi_i[i].rvfi_rd_addr, rvfi_i[i].rvfi_rd_wdata);
        else if (rvfi_i[i].rvfi_rd_addr != 0)
          $fwrite(f, " x%d 0x%h\n",
            rvfi_i[i].rvfi_rd_addr, rvfi_i[i].rvfi_rd_wdata);
        else $fwrite(f, "\n");
      end else if (rvfi_i[i].rvfi_trap)
        $fwrite(f, "exception : 0x%h\n", pc64);
    end
    if (cycles > SIM_FINISH) $finish(1);
  end

  //Trace custom signals
  //Define signals to be traced by adding them into debug and name arrays
  string name[0:10];
  logic[63:0] debug[0:10], debug_previous[0:10];
  //assign debug[0] = i_ariane.csr_regfile_i.dscratch1_q;
  //assign  name[0] = "i_ariane.csr_regfile_i.dscratch1_q";

  always_ff @(posedge i_ariane.clk_i) begin
    if (cycles > DEBUG_START && cycles < DEBUG_STOP)
      for (int index=0; index<100; index=index+1)
        if (debug_previous[index] != debug[index])
          $fwrite(f, "%d %s %x\n", cycles, name[index], debug[index]);
    debug_previous <= debug;
  end

endmodule // rvfi_tracer
