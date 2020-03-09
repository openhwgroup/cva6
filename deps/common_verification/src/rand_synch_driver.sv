// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Randomizing Synchronous Driver
module rand_synch_driver #(
  parameter type  data_t = logic,
  // Minimum number of clock cycles to wait between applying two consecutive values.
  parameter int   MIN_WAIT_CYCLES = -1,
  // Maximum number of clock cycles to wait between applying two consecutive values.
  parameter int   MAX_WAIT_CYCLES = -1,
  // Application delay: time delay before output changes after an active clock edge.
  parameter time  APPL_DELAY = 0ns
) (
  input  logic    clk_i,
  input  logic    rst_ni,

  output data_t   data_o
);

  rand_synch_holdable_driver #(
    .data_t           (data_t),
    .MIN_WAIT_CYCLES  (MIN_WAIT_CYCLES),
    .MAX_WAIT_CYCLES  (MAX_WAIT_CYCLES),
    .APPL_DELAY       (APPL_DELAY)
  ) i_ready_driver (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .hold_i (1'b0),
    .data_o (data_o)
  );

endmodule
