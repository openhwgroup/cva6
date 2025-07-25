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

module tb_atb_transmitter ();

    logic clk;
    logic reset;

    // inputs
    logic                           atready_i;
    logic                           afvalid_i;
    logic                           fifo_empty_i;
    logic [SLICE_LEN-1:0]           slice_i;
    logic [$clog2(SLICE_LEN)-4:0]   valid_bytes_i;
    logic [6:0]                     atid_i;

    // outputs
    logic [$clog2(SLICE_LEN)-4:0]   atbytes_o;
    logic [SLICE_LEN-1:0]           atdata_o;
    logic [6:0]                     atid_o;
    logic                           atvalid_o;
    logic                           afready_o;
    logic                           fifo_pop_o;

    // expected output
    logic [$clog2(SLICE_LEN)-4:0]   expected_atbytes;
    logic [SLICE_LEN-1:0]           expected_atdata;
    logic [6:0]                     expected_atid;
    logic                           expected_atvalid;
    logic                           expected_afready;
    logic                           expected_fifo_pop;

    // iteration variable
    logic [31:0] i;

    // DUT instantiation
    atb_transmitter #(
        .DATA_LEN(SLICE_LEN)
    ) DUT (
        .clk_i        (clk),
        .rst_ni       (reset),
        .atready_i    (atready_i),
        .afvalid_i    (afvalid_i),
        .fifo_empty_i (fifo_empty_i),
        .slice_i      (slice_i),
        .valid_bytes_i(valid_bytes_i),
        .atid_i       (atid_i),
        .atbytes_o    (atbytes_o),
        .atdata_o     (atdata_o),
        .atid_o       (atid_o),
        .atvalid_o    (atvalid_o),
        .afready_o    (afready_o),
        .fifo_pop_o   (fifo_pop_o)
    );

    logic [87:0] test_vector[1000:0];

    initial begin
        $readmemb("tb/testvectors/tv_atb_transmitter.txt", test_vector);
        i = 0;
        reset = 0; #10;
        reset = 1;   
    end

    always @(posedge clk) begin // on posedge we get expected output
        {
            atready_i,
            afvalid_i,
            fifo_empty_i,
            slice_i,
            valid_bytes_i,
            atid_i,
            expected_atbytes,
            expected_atdata,
            expected_atid,
            expected_atvalid,
            expected_afready,
            expected_fifo_pop
        } = test_vector[i]; #10; 
    end

    always @(negedge clk) begin// on negedge we compare the expected result with the actual one
        // index increase
        i = i + 1;
    end

    always begin
        clk <= 1; #5;
        clk <= 0; #5;
    end

endmodule