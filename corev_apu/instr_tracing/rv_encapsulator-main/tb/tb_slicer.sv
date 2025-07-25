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

import encap_pkg::*;

localparam SLICE_LEN = 32;

module tb_slicer ();

    logic clk;
    logic reset;

    // inputs
    logic                           valid_i;
    header_s                        header_i;
    logic [T_LEN-1:0]               timestamp_i;
    payload_s                       payload_i;
    logic                           fifo_full_i;

    // outputs
    logic                           valid_o;
    logic [SLICE_LEN-1:0]           slice_o;
    logic [$clog2(SLICE_LEN)-4:0]   valid_bytes_o;
    logic                           ready_o;

    // testing only outputs
    logic                           expected_valid;
    logic [SLICE_LEN-1:0]           expected_slice;
    logic [$clog2(SLICE_LEN)-4:0]   expected_valid_bytes;
    logic                           expected_ready;

    // iteration variable
    logic [31:0] i;

    // DUT instantiation
    slicer #(
        .SLICE_LEN(SLICE_LEN)
    ) DUT (
        .clk_i        (clk),
        .rst_ni       (reset),
        .valid_i      (valid_i),
        .header_i     (header_i),
        .timestamp_i  (timestamp_i),
        .payload_i    (payload_i),
        .fifo_full_i  (fifo_full_i),
        .valid_o      (valid_o),
        .slice_o      (slice_o),
        .valid_bytes_o(valid_bytes_o),
        .ready_o      (ready_o)
    );

    logic [357:0] test_vector[1000:0];

    initial begin
        $readmemb("tb/testvectors/tv_slicer.txt", test_vector);
        i = 0;
        reset = 0; #10;
        reset = 1;   
    end

    always @(posedge clk) begin // on posedge we get expected output
        {
            valid_i,
            header_i,
            timestamp_i,
            payload_i,
            fifo_full_i,
            expected_valid,
            expected_slice,
            expected_valid_bytes,
            expected_ready
        } = test_vector[i]; #10; 
    end

    always @(negedge clk) begin// on negedge we compare the expected result with the actual one
        // valid_o
        if(expected_valid !== valid_o) begin
            $display("Wrong valid_o: %b!=%b", expected_valid, valid_o);
        end
        // slice_o
        if(expected_slice !== slice_o) begin
            $display("Wrong slice_o: %b!=%b", expected_slice, slice_o);
        end
        // ready_o
        if(expected_ready !== ready_o) begin
            $display("Wrong ready_o: %b!=%b", expected_ready, ready_o);
        end

        // index increase
        i = i + 1;
    end

    always begin
        clk <= 1; #5;
        clk <= 0; #5;
    end

endmodule