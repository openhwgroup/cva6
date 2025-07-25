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
localparam N = 2;

module tb_te_branch_map();

    logic clk;
    logic reset;

    // inputs
    logic [N-1:0]   valid_i;
    logic [N-1:0]   branch_taken_i;
    logic flush_i;

    // outputs
    logic [BRANCH_MAP_LEN-1:0]      map_o;
    logic [BRANCH_COUNT_LEN-1:0]    branches_o;
    logic                           is_full_o;
    logic                           is_empty_o;

    // testing only outputs
    logic [BRANCH_MAP_LEN-1:0]      expected_map;
    logic [BRANCH_COUNT_LEN-1:0]    expected_branches;
    logic                           expected_is_full;
    logic                           expected_is_empty;

    // iteration variable
    logic [31:0] i;

    // DUT instantiation
    te_branch_map #(
        .N(2)
    ) DUT(
        .clk_i         (clk),
        .rst_ni        (reset),
        .valid_i       (valid_i),
        .branch_taken_i(branch_taken_i),
        .flush_i       (flush_i),
        .map_o         (map_o),
        .branches_o    (branches_o),
        .is_full_o     (is_full_o),
        .is_empty_o    (is_empty_o)
    );

    logic [42:0] test_vector[1000:0];
    //    length of line   # of lines

    initial begin // reading test vector
        $readmemb("./tb/testvectors/tv_te_branch_map.txt", test_vector);
        i = 0;
        reset = 0; #10;
        reset = 1;            
    end

    always @(posedge clk) begin // on posedge we get expected output
        {
            valid_i,
            branch_taken_i,
            flush_i,
            expected_map,
            expected_branches,
            expected_is_full,
            expected_is_empty
        } = test_vector[i]; #10; 
    end

    always @(negedge clk) begin// on negedge we compare the expected result with the actual one
        // map_o
        if(expected_map !== map_o) begin
            $display("Wrong branch map: %b!=%b", expected_map, map_o); // printed if it's wrong
        end        
        // branches_o
        if(expected_branches !== branches_o) begin
            $display("Wrong branch count: %b!=%b", expected_branches, branches_o);
        end
        // is_full_o
        if(expected_is_full !== is_full_o) begin
            $display("Wrong is_full: %b!=%b", expected_is_full, is_full_o);
        end
        // is_empty_o
        if(expected_is_empty !== is_empty_o) begin
            $display("Wrong is_empty: %b!=%b", expected_is_empty, is_empty_o);
        end
        // index increase
        i = i + 1;
    end

    always begin
        clk <= 1; #5;
        clk <= 0; #5;
    end

endmodule