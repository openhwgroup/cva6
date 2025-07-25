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

module tb_te_packet_emitter();

    logic clk;
    logic reset;

    // inputs
    logic                           valid_i;
    format_e                        packet_format_i;
    f_sync_subformat_e              packet_subformat_i;
    logic [XLEN-1:0]                lc_cause_i;
    logic [XLEN-1:0]                lc_tval_i;
    logic                           lc_interrupt_i;
    logic [XLEN-1:0]                tc_cause_i;
    logic [XLEN-1:0]                tc_tval_i;
    logic                           tc_interrupt_i;
    logic                           nocontext_i;
    logic                           notime_i;
    logic                           tc_branch_i;
    logic                           tc_branch_taken_i;
    logic [1:0]                     tc_priv_i;
    logic [XLEN-1:0]                time_i;
    logic [XLEN-1:0]                tc_address_i;
    logic                           lc_tc_mux_i;
    logic                           thaddr_i;
    logic [XLEN-1:0]                tc_tvec_i;
    logic [XLEN-1:0]                lc_epc_i;
    logic                           tc_ienable_i;
    logic                           encoder_mode_i;
    qual_status_e                   qual_status_i;
    ioptions_s                      ioptions_i;
    logic                           lc_updiscon_i;
    logic [BRANCH_COUNT_LEN-1:0]    branches_i;
    logic [BRANCH_MAP_LEN-1:0]      branch_map_i;
    logic [$clog2(XLEN):0]          keep_bits_i;
    logic                           shallow_trace_i;

    // outputs
    logic                   packet_valid_o;
    it_packet_type_e        packet_type_o;
    logic [PAYLOAD_LEN-1:0] packet_payload_o;
    logic [P_LEN-1:0]       payload_length_o;
    logic                   branch_map_flush_o;
    logic [XLEN:0]          addr_to_compress_o;

    // testing only output
    logic                   expected_packet_valid;
    it_packet_type_e        expected_packet_type;
    logic [PAYLOAD_LEN-1:0] expected_packet_payload;
    logic [P_LEN-1:0]       expected_payload_length;
    logic                   expected_branch_map_flush;
    logic [XLEN:0]          expected_addr_to_compress;

    // iteration variable
    logic [31:0] i;

    // DUT instantiation
    te_packet_emitter DUT(
        .clk_i                    (clk),
        .rst_ni                   (reset),
        .valid_i                  (valid_i),
        .packet_format_i          (packet_format_i),
        .packet_f_sync_subformat_i(packet_subformat_i),
        .lc_cause_i               (lc_cause_i),
        .lc_tval_i                (lc_tval_i),
        .lc_interrupt_i           (lc_interrupt_i),
        .tc_cause_i               (tc_cause_i),
        .tc_tval_i                (tc_tval_i),
        .tc_interrupt_i           (tc_interrupt_i),
        .nocontext_i              (nocontext_i),
        .notime_i                 (notime_i),
        .tc_branch_i              (tc_branch_i),
        .tc_branch_taken_i        (tc_branch_taken_i),
        .tc_priv_i                (tc_priv_i),
        .time_i                   (time_i),
        .tc_address_i             (tc_address_i),
        .lc_tc_mux_i              (lc_tc_mux_i),
        .thaddr_i                 (thaddr_i),
        .tc_tvec_i                (tc_tvec_i),
        .lc_epc_i                 (lc_epc_i),
        .tc_ienable_i             (tc_ienable_i),
        .encoder_mode_i           (encoder_mode_i),
        .qual_status_i            (qual_status_i),
        .ioptions_i               (ioptions_i),
        .lc_updiscon_i            (lc_updiscon_i),
        .branches_i               (branches_i),
        .branch_map_i             (branch_map_i),
        .keep_bits_i              (keep_bits_i),
        .shallow_trace_i          (shallow_trace_i),
        .packet_valid_o           (packet_valid_o),
        .packet_type_o            (packet_type_o),
        .packet_payload_o         (packet_payload_o),
        .payload_length_o         (payload_length_o),
        .branch_map_flush_o       (branch_map_flush_o),
        .addr_to_compress_o       (addr_to_compress_o)
    );

    logic [569:0] test_vector[1000:0];
    //     length of line    # of lines

    initial begin // reading test vector
        $readmemb("./tb/testvectors/tv_te_packet_emitter.txt", test_vector);
        i = 0;
        reset = 0; #10;
        reset = 1;  // set == 1 -> no reset each cycle
                    // set == 0 -> reset each cycle
    end

    always @(posedge clk) begin
        {
            valid_i,
            packet_format_i,
            packet_subformat_i,
            lc_cause_i,
            lc_tval_i,
            lc_interrupt_i,
            tc_cause_i,
            tc_tval_i,
            tc_interrupt_i,
            nocontext_i,
            notime_i,
            tc_branch_i,
            tc_branch_taken_i,
            tc_priv_i,
            time_i,
            tc_address_i,
            lc_tc_mux_i,
            thaddr_i,
            tc_tvec_i,
            lc_epc_i,
            tc_ienable_i,
            encoder_mode_i,
            qual_status_i,
            ioptions_i,
            lc_updiscon_i,
            branches_i,
            branch_map_i,
            keep_bits_i,
            shallow_trace_i,
            expected_packet_valid,
            expected_packet_type,
            expected_packet_payload,
            expected_payload_length,
            expected_branch_map_flush,
            expected_addr_to_compress
        } = test_vector[i]; #10;
        
    end

    always @(negedge clk) begin // prints the line if it's wrong
        // packet_valid_o
        if(expected_packet_valid !== packet_valid_o) begin
            $display("Wrong valid: %b!=%b", expected_packet_valid, packet_valid_o);
        end
        // packet_type_o
        if(expected_packet_type !== packet_type_o) begin
            $display("Wrong valid: %b!=%b", expected_packet_type, packet_type_o);
        end
        // packet_payload_o
        if(expected_packet_payload !== packet_payload_o) begin
            $display("Wrong payload: %b!=%b", expected_packet_payload, packet_payload_o);
        end
        // payload_length_o
        if(expected_payload_length !== payload_length_o) begin
            $display("Wrong payload length: %b!=%b", expected_payload_length, payload_length_o);
        end
        // branch_map_flush_o
        if(expected_branch_map_flush !== branch_map_flush_o) begin
            $display("Wrong branch map flush: %b!=%b", expected_branch_map_flush, branch_map_flush_o);
        end
        // addr_to_compress_o
        if(expected_addr_to_compress !== addr_to_compress_o) begin
            $display("Wrong address to compress: %b!=%b", expected_addr_to_compress, addr_to_compress_o);
        end

        // index increase
        i = i + 1;
    end

    always begin
        clk <= 1; #5;
        clk <= 0; #5;
    end

endmodule