// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Package with functions and tasks commonly used in constrained randomized verification
package rand_verif_pkg;

  // Pick a random number from the interval [min, max] and wait for that number of clock cyles.
  task automatic rand_wait(input int unsigned min, max, ref logic clk);
      int unsigned rand_success, cycles;
      rand_success = randomize(cycles) with {
          cycles >= min;
          cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge clk);
  endtask

endpackage
