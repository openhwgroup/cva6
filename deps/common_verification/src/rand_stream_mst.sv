// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Randomizing Stream (Ready/Valid) Master
module rand_stream_mst #(
  parameter type  data_t = logic,
  // Minimum number of clock cycles to wait between applying two consecutive values.
  parameter int   MIN_WAIT_CYCLES = -1,
  // Maximum number of clock cycles to wait between applying two consecutive values.
  parameter int   MAX_WAIT_CYCLES = -1,
  // Application delay: time delay before output changes after an active clock edge.
  parameter time  APPL_DELAY = 0ns,
  // Acquisition delay: time delay before ready input is read after an active clock edge.
  parameter time  ACQ_DELAY = 0ns
) (
  input  logic    clk_i,
  input  logic    rst_ni,

  output data_t   data_o,
  output logic    valid_o,
  input  logic    ready_i
);

  timeunit 1ns;
  timeprecision 10ps;

  int unsigned rand_wait_cycles;

  function static void randomize_wait_cycles();
    int unsigned rand_success;
    rand_success = std::randomize(rand_wait_cycles) with {
      rand_wait_cycles >= MIN_WAIT_CYCLES;
      rand_wait_cycles <= MAX_WAIT_CYCLES;
    };
    assert (rand_success) else $error("Failed to randomize wait cycles!");
  endfunction

  initial begin
    data_o  = '0;
    valid_o = 1'b0;
    wait (rst_ni);
    // Initially pick a random number of cycles to wait until we offer the first valid data.
    randomize_wait_cycles();
    @(posedge clk_i);
    forever begin
      // Wait for the picked number of clock cycles.
      repeat(rand_wait_cycles) begin
        @(posedge clk_i);
      end
      // Delay application of data and valid output.
      #(APPL_DELAY);
      // Randomize data output and set valid output.
      void'(std::randomize(data_o));
      valid_o = 1'b1;
      // Delay acquisition of ready signal. ACQ_DELAY is relative to the clock edge, and we have
      // already waited for APPL_DELAY in this edge, so we need to subtract APPL_DELAY.
      #(ACQ_DELAY-APPL_DELAY);
      // Sample the ready input. While the slave is not ready, wait a clock cycle plus the
      // acquisition delay and resample the ready input.
      while (!ready_i) begin
        @(posedge clk_i);
        #(ACQ_DELAY);
      end
      // The slave is ready to acquire data on the next rising edge, so we pick a new number of
      // cycles to wait until we offer the next valid data.
      randomize_wait_cycles();
      if (rand_wait_cycles == 0) begin
        // If we have to wait 0 cycles, we apply new data directly after next clock edge plus the
        // application delay.
        @(posedge clk_i);
      end else begin
        // If we have to wait more than 0 cycles, we unset the valid output and randomize the data
        // output after the next clock edge plus the application delay.
        @(posedge clk_i);
        #(APPL_DELAY);
        valid_o = 1'b0;
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
    assert (ACQ_DELAY > 0ns)
      else $fatal("The acquisition delay must be greater than 0!");
    assert (ACQ_DELAY > APPL_DELAY)
      else $fatal("The acquisition delay must be greater than the application delay!");
  end
`endif

endmodule
