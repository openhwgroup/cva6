// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Randomizing Synchronous Holdable Driver
module rand_synch_holdable_driver #(
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

  input  logic    hold_i,
  output data_t   data_o
);

  timeunit 1ns;
  timeprecision 10ps;

  initial begin
    int unsigned rand_delay, rand_success;
    data_o = '0;
    wait (rst_ni);
    @(posedge clk_i);
    forever begin
      rand_success = std::randomize(rand_delay) with {
        rand_delay >= MIN_WAIT_CYCLES;
        rand_delay <= MAX_WAIT_CYCLES;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat(rand_delay) begin
        @(posedge clk_i);
      end
      #(APPL_DELAY);
      if (!hold_i) begin
        void'(std::randomize(data_o));
      end
    end
  end

  // Validate parameters.
`ifndef VERILATOR
  initial begin: validate_params
    assert (MIN_WAIT_CYCLES >= 0)
      else $fatal("The minimum number of wait cycles must be at least 0!");
    assert (MAX_WAIT_CYCLES >= 0)
      else $fatal("The maximum number of wait cycles must be at least 0!");
    assert (MAX_WAIT_CYCLES >= MIN_WAIT_CYCLES)
      else $fatal("The maximum number of wait cycles must be at least the minimum number of wait cycles!");
    assert (APPL_DELAY > 0ns)
      else $fatal("The application delay must be greater than 0!");
  end
`endif

endmodule
