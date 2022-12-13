// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module tc_clk_and2 (
  input  logic clk0_i,
  input  logic clk1_i,
  output logic clk_o
);

  assign clk_o = clk0_i & clk1_i;

endmodule

module tc_clk_buffer (
  input  logic clk_i,
  output logic clk_o
);

  assign clk_o = clk_i;

endmodule

// Description: Behavioral model of an integrated clock-gating cell (ICG)
module tc_clk_gating #(
  /// This paramaeter is a hint for tool/technology specific mappings of this
  /// tech_cell. It indicates wether this particular clk gate instance is
  /// required for functional correctness or just instantiated for power
  /// savings. If IS_FUNCTIONAL == 0, technology specific mappings might
  /// replace this cell with a feedthrough connection without any gating.
  parameter bit IS_FUNCTIONAL = 1'b1
)(
   input  logic clk_i,
   input  logic en_i,
   input  logic test_en_i,
   output logic clk_o
);

  logic clk_en;

  always_latch begin
    if (clk_i == 1'b0) clk_en <= en_i | test_en_i;
  end

  assign clk_o = clk_i & clk_en;

endmodule

module tc_clk_inverter (
  input  logic clk_i,
  output logic clk_o
);

  assign clk_o = ~clk_i;

endmodule

module tc_clk_mux2 (
  input  logic clk0_i,
  input  logic clk1_i,
  input  logic clk_sel_i,
  output logic clk_o
);

  assign clk_o = (clk_sel_i) ? clk1_i : clk0_i;

endmodule

module tc_clk_xor2 (
  input  logic clk0_i,
  input  logic clk1_i,
  output logic clk_o
);

  assign clk_o = clk0_i ^ clk1_i;

endmodule

`ifndef SYNTHESIS
module tc_clk_delay #(
  parameter int unsigned Delay = 300ps
) (
  input  logic in_i,
  output logic out_o
);

// pragma translate_off
`ifndef VERILATOR
  assign #(Delay) out_o = in_i;
`endif
// pragma translate_on

endmodule
`endif


