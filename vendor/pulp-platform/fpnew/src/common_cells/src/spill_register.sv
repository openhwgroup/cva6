// Copyright 2018 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>


/// A register with handshakes that completely cuts any combinational paths
/// between the input and output.
module spill_register #(
  parameter type T = logic
)(
  input  logic clk_i   ,
  input  logic rst_ni  ,
  input  logic valid_i ,
  output logic ready_o ,
  input  T     data_i  ,
  output logic valid_o ,
  input  logic ready_i ,
  output T     data_o
);

  // The A register.
  T a_data_q;
  logic a_full_q;
  logic a_fill, a_drain;
  logic a_en, a_en_data;

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_a_data
    if (!rst_ni)
      a_data_q <= '0;
    else if (a_fill)
      a_data_q <= data_i;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_a_full
    if (!rst_ni)
      a_full_q <= 0;
    else if (a_fill || a_drain)
      a_full_q <= a_fill;
  end

  // The B register.
  T b_data_q;
  logic b_full_q;
  logic b_fill, b_drain;

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_b_data
    if (!rst_ni)
      b_data_q <= '0;
    else if (b_fill)
      b_data_q <= a_data_q;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : ps_b_full
    if (!rst_ni)
      b_full_q <= 0;
    else if (b_fill || b_drain)
      b_full_q <= b_fill;
  end

  // Fill the A register when the A or B register is empty. Drain the A register
  // whenever it is full and being filled.
  assign a_fill = valid_i && ready_o;
  assign a_drain = a_full_q && !b_full_q;

  // Fill the B register whenever the A register is drained, but the downstream
  // circuit is not ready. Drain the B register whenever it is full and the
  // downstream circuit is ready.
  assign b_fill = a_drain && !ready_i;
  assign b_drain = b_full_q && ready_i;

  // We can accept input as long as register B is not full.
  assign ready_o = !a_full_q || !b_full_q;

  // The unit provides output as long as one of the registers is filled.
  assign valid_o = a_full_q | b_full_q;

  // We empty the spill register before the slice register.
  assign data_o = b_full_q ? b_data_q : a_data_q;

endmodule
