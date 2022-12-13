// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module pulp_clock_and2 (
  input  logic clk0_i,
  input  logic clk1_i,
  output logic clk_o
);

  tc_clk_and2 i_tc_clk_and2 (
    .clk0_i,
    .clk1_i,
    .clk_o
  );

endmodule

module pulp_clock_buffer (
  input  logic clk_i,
  output logic clk_o
);

  tc_clk_buffer i_tc_clk_buffer (
    .clk_i,
    .clk_o
  );

endmodule

// Description: Behavioral model of an integrated clock-gating cell (ICG)
module pulp_clock_gating (
   input  logic clk_i,
   input  logic en_i,
   input  logic test_en_i,
   output logic clk_o
);

  tc_clk_gating i_tc_clk_gating (
     .clk_i,
     .en_i,
     .test_en_i,
     .clk_o
  );

endmodule

module pulp_clock_inverter (
  input  logic clk_i,
  output logic clk_o
);

  tc_clk_inverter i_tc_clk_inverter (
    .clk_i,
    .clk_o
  );

endmodule

module pulp_clock_mux2 (
  input  logic clk0_i,
  input  logic clk1_i,
  input  logic clk_sel_i,
  output logic clk_o
);

  tc_clk_mux2 i_tc_clk_mux2 (
    .clk0_i,
    .clk1_i,
    .clk_sel_i,
    .clk_o
  );

endmodule

module pulp_clock_xor2 (
  input  logic clk0_i,
  input  logic clk1_i,
  output logic clk_o
);

  tc_clk_xor2 i_tc_clk_xor2 (
    .clk0_i,
    .clk1_i,
    .clk_o
  );

endmodule

`ifndef SYNTHESIS
module pulp_clock_delay(
  input  logic in_i,
  output logic out_o
);

  assign #(300ps) out_o = in_i;

endmodule
`endif


