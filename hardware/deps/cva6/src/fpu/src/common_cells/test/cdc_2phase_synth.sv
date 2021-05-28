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

module cdc_2phase_synth (
  input  logic        src_rst_ni,
  input  logic        src_clk_i,
  input  logic [31:0] src_data_i,
  input  logic        src_valid_i,
  output logic        src_ready_o,

  input  logic        dst_rst_ni,
  input  logic        dst_clk_i,
  output logic [31:0] dst_data_o,
  output logic        dst_valid_o,
  input  logic        dst_ready_i
);

  cdc_2phase #(logic [31:0]) i_cdc (.*);

endmodule
