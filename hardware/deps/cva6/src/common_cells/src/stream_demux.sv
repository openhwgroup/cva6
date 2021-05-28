// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/// Stream demultiplexer: Connects the input stream (valid-ready) handshake to one of `N_OUP` output
/// stream handshakes.
///
/// This module has no data ports because stream data does not need to be demultiplexed: the data of
/// the input stream can just be applied at all output streams.

module stream_demux #(
  parameter integer N_OUP = 1,
  /// Dependent parameters, DO NOT OVERRIDE!
  parameter integer LOG_N_OUP = $clog2(N_OUP)
) (
  input  logic                  inp_valid_i,
  output logic                  inp_ready_o,

  input  logic  [LOG_N_OUP-1:0] oup_sel_i,

  output logic  [N_OUP-1:0]     oup_valid_o,
  input  logic  [N_OUP-1:0]     oup_ready_i
);

  always_comb begin
    oup_valid_o = '0;
    oup_valid_o[oup_sel_i] = inp_valid_i;
  end
  assign inp_ready_o = oup_ready_i[oup_sel_i];

endmodule
