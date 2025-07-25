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

module tb_encapsulator ();

    logic clk;
    logic reset;

    // inputs
    logic                   valid_i;
    logic [P_LEN-1:0]       packet_length_i;
    logic [FLOW_LEN-1:0]    flow_i;
    logic                   timestamp_present_i;
    //logic                   srcid_i;
    logic [T_LEN-1:0]       timestamp_i;
    logic                   instr_tracing_only_i;
    //logic [TYPE_LEN-1:0]    type_i;
    logic [PAYLOAD_LEN-1:0] trace_payload_i;

    // outputs
    logic                   valid_o;
    header_s                header_o;
    //logic [SRCID_LEN-1:0]   srcid_o;
    logic [T_LEN-1:0]       timestamp_o;
    payload_s               payload_o;

    // testing only outputs
    logic                   expected_valid;
    header_s                expected_header;
    //logic [SRCID_LEN-1:0]   expected_srcid;
    logic [T_LEN-1:0]       expected_timestamp;
    payload_s               expected_payload;

    // iteration variable
    logic [31:0] i;

    // DUT instantiation
    encapsulator DUT (
        .valid_i            (valid_i),
        .packet_length_i    (packet_length_i),
        .flow_i             (flow_i),
        .timestamp_present_i(timestamp_present_i),
        //.srcid_i            (srcid_i),
        .timestamp_i        (timestamp_i),
        //.type_i             (type_i),
        .trace_payload_i    (trace_payload_i),
        .valid_o            (valid_o),
        .header_o           (header_o),
        //.srcid_o            (srcid_o),
        .timestamp_o        (timestamp_o),
        .payload_o          (payload_o)
    );

    logic [641:0] test_vector[1000:0];

    initial begin
        $readmemb("tb/testvectors/tv_encapsulator.txt", test_vector);
        i = 0;
        reset = 0; #10;
        reset = 1;   
    end

    always @(posedge clk) begin // on posedge we get expected output
        {
            valid_i,
            packet_length_i,
            flow_i,
            timestamp_present_i,
            //srcid_i,
            timestamp_i,
            //type_i,
            trace_payload_i,
            expected_valid,
            expected_header,
            //expected_srcid,
            expected_timestamp,
            expected_payload
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