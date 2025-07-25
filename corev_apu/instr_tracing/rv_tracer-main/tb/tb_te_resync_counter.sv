// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51

// Author:  Umberto Laghi
// Contact: umberto.laghi2@unibo.it
// Github:  @ubolakes

`timescale 1ns/1ns

import te_pkg::*;
parameter N = 4;

module tb_te_resync_counter();

    logic clk;
    logic reset;

    // inputs
    logic           trace_enabled_i;
    logic [N-1:0]   packet_emitted_i;
    logic           resync_rst_i;
    // outputs
    logic           gt_resync_max_o;
    logic           et_resync_max_o;
    // testing only outputs
    logic           expected_gt_resync_max;
    logic           expected_et_resync_max;

    // iteration variable
    logic [31:0] i;

    // DUT instantiation
    te_resync_counter #(
        .N(N),
        .MODE(CYCLE_MODE), // counting packets
        .MAX_VALUE(7) // counting up to 7
    ) DUT(
        .clk_i           (clk),
        .rst_ni          (reset),
        .trace_enabled_i (trace_enabled_i),
        .packet_emitted_i(packet_emitted_i),
        .resync_rst_i    (resync_rst_i),
        .gt_resync_max_o (gt_resync_max_o),
        .et_resync_max_o (et_resync_max_o)
    );


    logic [7:0] test_vector[1000:0];
    //    length of line   # of lines

    initial begin // reading test vector
        $readmemb("./tb/testvectors/tv_te_resync_counter.txt", test_vector);
        i = 0;
        reset = 0; #10;
        reset = 1;            
    end

    always @(posedge clk) begin // on posedge we get expected output
        {
            trace_enabled_i,
            packet_emitted_i,
            resync_rst_i,
            expected_gt_resync_max,
            expected_et_resync_max
        } = test_vector[i]; #10; 
    end

    always @(negedge clk) begin// on negedge we compare the expected result with the actual one
        // gt_resync_max_o
        if(expected_gt_resync_max !== gt_resync_max_o) begin
            $display("Wrong gt_resync_max: %b!=%b", expected_gt_resync_max, gt_resync_max_o); // printed if it's wrong
        end        
        // et_resync_max_o
        if(expected_et_resync_max !== et_resync_max_o) begin
            $display("Wrong branch count: %b!=%b", expected_et_resync_max, et_resync_max_o);
        end
        // index increase
        i = i + 1;
    end

    always begin
        clk <= 1; #5;
        clk <= 0; #5;
    end

endmodule