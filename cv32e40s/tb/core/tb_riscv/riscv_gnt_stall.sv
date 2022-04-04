//
// Copyright 2020 OpenHW Group
// Copyright 2020 Silicon Labs, Inc.
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
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//
// riscv_gnt_stall.sv
//
// OBI Grant stalling module for CV32E40S
//
// Author: Steve Richmond
//   email: steve.richmond@silabs.com
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////


module riscv_gnt_stall
`ifndef VERILATOR
 import perturbation_defines::*;
`endif
 #(
    parameter MAX_STALL_N    = 1,
              RAM_ADDR_WIDTH = 32,
              DATA_WIDTH     = 32
  )

(
    input logic                             clk_i,
    input logic                             rst_ni,

    input logic                             req_core_i,
    output logic                            req_mem_o,

    // grant to memory
    output logic                            grant_core_o,
    input logic                             grant_mem_i,

    input logic                             en_stall_i,
    input logic [31:0]                      stall_mode_i,
    input logic [31:0]                      max_stall_i,
    input logic [31:0]                      gnt_stall_i
);

// -----------------------------------------------------------------------------------------------
// Local variables
// -----------------------------------------------------------------------------------------------

logic req_core_i_q;
logic grant_core_o_q;

integer grant_delay_cnt;

integer delay_value;

// -----------------------------------------------------------------------------------------------
// Tasks and functions
// -----------------------------------------------------------------------------------------------
task set_delay_value();
`ifndef VERILATOR
  if (!en_stall_i)
    delay_value = 0;
  else if (stall_mode_i == perturbation_defines::STANDARD)
    delay_value = gnt_stall_i;
  else if (stall_mode_i == perturbation_defines::RANDOM)
    delay_value = $urandom_range(max_stall_i, 0);
  else
    delay_value = 0;
`else
    delay_value = 0;
`endif
endtask : set_delay_value

// -----------------------------------------------------------------------------------------------
// Begin module code
// -----------------------------------------------------------------------------------------------

assign req_mem_o   = req_core_i;

always @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    req_core_i_q <= 1'b0;
    grant_core_o_q <= 1'b0;
  end
  else begin
    req_core_i_q <= req_core_i;
    grant_core_o_q <= grant_core_o;
  end
end

always @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    grant_core_o <= 1'b0;
    grant_delay_cnt <= 0;
  end
  else begin
`ifdef VERILATOR
    //#1;
`else
    #(100ps);
`endif

    // When request is removed, randomize gnt
    if (!req_core_i) begin
      grant_core_o <= $urandom;
    end

    // New request coming in
    else if (grant_core_o_q || !req_core_i_q) begin
      // Initialize stall here
      set_delay_value();
      if (delay_value == 0) begin
        grant_delay_cnt <= 0;
        grant_core_o <= 1'b1;
      end
      else begin
        grant_delay_cnt <= delay_value;
        grant_core_o <= 1'b0;
      end
    end
    else if (grant_delay_cnt == 1) begin
      grant_delay_cnt <= 0;
      grant_core_o <= 1'b1;
    end
    else begin
      grant_delay_cnt <= grant_delay_cnt - 1;
    end
  end
end

endmodule : riscv_gnt_stall
