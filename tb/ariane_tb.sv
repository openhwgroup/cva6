// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 15/04/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+


import ariane_pkg::*;
import uvm_pkg::*;

`include "uvm_macros.svh"

module ariane_tb;

    // static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();

    localparam int unsigned CLOCK_PERIOD = 20ns;

    logic clk_i;
    logic rst_ni;
    logic [63:0] time_i;

    longint unsigned cycles;
    longint unsigned max_cycles;

    logic [31:0] exit_o;

    ariane_testharness dut (
        .clk_i                   ( clk_i                        ),
        .rst_ni                  ( rst_ni                       ),
        .exit_o                  ( exit_o                       )
    );

    // Clock process
    initial begin
        clk_i = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #(CLOCK_PERIOD/2) clk_i = ~clk_i;
        rst_ni = 1'b1;
        forever begin
            #(CLOCK_PERIOD/2) clk_i = 1'b1;
            #(CLOCK_PERIOD/2) clk_i = 1'b0;

            //if (cycles > max_cycles)
            //    $fatal(1, "Simulation reached maximum cycle count of %d", max_cycles);

            cycles++;
        end
    end
    // Real Time Clock
    initial begin
        // initialize platform timer
        time_i = 64'b0;
        // increment timer with a frequency of 32.768 kHz
        forever begin
            #30.517578us;
            time_i++;
        end
    end

    initial begin
        forever begin

            wait (exit_o[0]);

            if ((exit_o >> 1)) begin
                `uvm_error( "Core Test",  $sformatf("*** FAILED *** (tohost = %0d)", (exit_o >> 1)))
            end else begin
                `uvm_info( "Core Test",  $sformatf("*** SUCCESS *** (tohost = %0d)", (exit_o >> 1)), UVM_LOW)
            end

            $finish();
        end
    end

endmodule
