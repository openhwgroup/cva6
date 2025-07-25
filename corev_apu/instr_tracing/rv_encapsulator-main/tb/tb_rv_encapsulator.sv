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

localparam DATA_LEN = 32;

module tb_rv_encapsulator ();

    logic clk;
    logic reset;

    // inputs
    logic                           valid_i;
    logic [P_LEN-1:0]               packet_length_i;
    logic                           notime_i;
    //logic                           srcid_i;
    logic [T_LEN-1:0]               timestamp_i;
    //logic [TYPE_LEN-1:0]            type_i;
    logic [PAYLOAD_LEN-1:0]         trace_payload_i;
    // atb interface
    logic                           atready_i;
    logic                           afvalid_i;
    
    // output
    logic [$clog2(DATA_LEN)-4:0]    atbytes_o;
    logic [DATA_LEN-1:0]            atdata_o;
    logic [6:0]                     atid_o;
    logic                           atvalid_o;
    logic                           afready_o;
    logic                           encapsulator_ready_o;

    // expected output
    logic [$clog2(DATA_LEN)-4:0]    expected_atbytes_o;
    logic [DATA_LEN-1:0]            expected_atdata_o;
    logic [6:0]                     expected_atid_o;
    logic                           expected_atvalid_o;
    logic                           expected_afready_o;
    logic                           expected_encapsulator_ready_o;
    
    // iteration variable
    logic [31:0] i;

    // DUT instantiation
    rv_encapsulator #(
        .DATA_LEN(DATA_LEN)
    ) DUT (
        .clk_i               (clk),
        .rst_ni              (reset),
        .valid_i             (valid_i),
        .packet_length_i     (packet_length_i),
        .notime_i            (notime_i),
        //.srcid_i(),
        .timestamp_i         (timestamp_i),
        //.type_i(),
        .trace_payload_i     (trace_payload_i),
        .atready_i           (atready_i),
        .afvalid_i           (afvalid_i),
        .atbytes_o           (atbytes_o),
        .atdata_o            (atdata_o),
        .atid_o              (atid_o),
        .atvalid_o           (atvalid_o),
        .afready_o           (afready_o),
        .encapsulator_ready_o(encapsulator_ready_o)
    );

    logic [364:0] test_vector[1000:0];

    initial begin
        $readmemb("tb/testvectors/tv_rv_encapsulator.txt", test_vector);
        i = 0;
        reset = 0; #10;
        reset = 1;   
    end

    always @(posedge clk) begin // on posedge we get expected output
        {
            valid_i,
            packet_length_i,
            notime_i,
            //srcid_i,
            timestamp_i,
            //type_i,
            trace_payload_i,
            atready_i,
            afvalid_i,
            expected_atbytes_o,
            expected_atdata_o,
            expected_atid_o,
            expected_atvalid_o,
            expected_afready_o,
            expected_encapsulator_ready_o
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