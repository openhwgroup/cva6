// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/// Stream multiplexer: connects the output to one of `N_INP` data streams with valid-ready
/// handshaking.

module stream_mux #(
  parameter type DATA_T = logic,  // Vivado requires a default value for type parameters.
  parameter integer N_INP = 0,    // Synopsys DC requires a default value for value parameters.
  /// Dependent parameters, DO NOT OVERRIDE!
  parameter integer LOG_N_INP = $clog2(N_INP)
) (
  input  DATA_T [N_INP-1:0]     inp_data_i,
  input  logic  [N_INP-1:0]     inp_valid_i,
  output logic  [N_INP-1:0]     inp_ready_o,

  input  logic  [LOG_N_INP-1:0] inp_sel_i,

  output DATA_T                 oup_data_o,
  output logic                  oup_valid_o,
  input  logic                  oup_ready_i
);

  always_comb begin
    inp_ready_o = '0;
    inp_ready_o[inp_sel_i] = oup_ready_i;
  end
  assign oup_data_o   = inp_data_i[inp_sel_i];
  assign oup_valid_o  = inp_valid_i[inp_sel_i];

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (N_INP >= 1) else $fatal ("The number of inputs must be at least 1!");
  end
`endif
// pragma translate_on

endmodule
