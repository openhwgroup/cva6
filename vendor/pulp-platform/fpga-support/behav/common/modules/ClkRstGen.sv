// Copyright 2016 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/**
 * Clock and Reset Generator
 *
 * This module generates a single-phase clock and an active-low reset signal for a simulation
 * testbench.
 *
 * Parameter Description:
 *  CLK_LOW_TIME  Duration of the phase in which the clock is low.
 *  CLK_HIGH_TIME Duration of the phase in which the clock is high.
 *  RST_TIME      Interval at the beginning of the simulation during which the reset is active.
 *
 * Port Description:
 *  EndOfSim_SI   Stops the simulation clock in the next period.
 *  Clk_CO        Single-phase clock.
 *  Rst_RBO       Active-low reset.
 */

//timeunit 1ns;

module ClkRstGen

  // Parameters {{{
  #(
    parameter CLK_LOW_TIME  = 5ns,
    parameter CLK_HIGH_TIME = 5ns,
    parameter RST_TIME      = 100ns
  )
  // }}}

  // Ports {{{
  (
    input  logic  EndOfSim_SI,
    output logic  Clk_CO,
    output logic  Rst_RBO
  );
  // }}}

  // Module-Wide Constants {{{
  localparam time CLK_PERIOD  = CLK_LOW_TIME + CLK_HIGH_TIME;
  // }}}

  // Clock Generation {{{
  always begin
    Clk_CO  = 0;
    if (Rst_RBO) begin
      // Reset is inactive.
      if (~EndOfSim_SI) begin
        Clk_CO = 1;
        #CLK_HIGH_TIME;
        Clk_CO = 0;
        #CLK_LOW_TIME;
      end else begin
        $stop(0);
      end
    end else begin
      // Reset is still active, wait until the next clock period.
      #CLK_PERIOD;
    end
  end
  // }}}

  // Reset Generation {{{
  initial begin
    Rst_RBO = 0;
    #RST_TIME;
    Rst_RBO = 1;
  end
  // }}}

endmodule

// vim: nosmartindent autoindent foldmethod=marker
