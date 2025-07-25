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

module tb_te_reg();

    logic clk;
    logic reset;

    // inputs
    logic           trace_req_off_i;
    logic           trace_req_on_i;
    logic           encapsulator_ready_i;
    logic [31:0]    paddr_i;
    logic           pwrite_i;
    logic           psel_i;
    logic           penable_i;
    logic [31:0]    pwdata_i;

    // outputs
    logic                   cause_filter_o;
    logic [XLEN-1:0]        upper_cause_o;
    logic [XLEN-1:0]        lower_cause_o;
    logic [XLEN-1:0]        match_cause_o;
    logic                   cause_mode_o;
    logic                   tvec_filter_o;
    logic [XLEN-1:0]        upper_tvec_o;
    logic [XLEN-1:0]        lower_tvec_o;
    logic [XLEN-1:0]        match_tvec_o;
    logic                   tvec_mode_o;
    logic                   tval_filter_o;
    logic [XLEN-1:0]        upper_tval_o;
    logic [XLEN-1:0]        lower_tval_o;
    logic [XLEN-1:0]        match_tval_o;
    logic                   tval_mode_o;
    logic                   priv_lvl_filter_o;
    logic [PRIV_LEN-1:0]    upper_priv_o;
    logic [PRIV_LEN-1:0]    lower_priv_o;
    logic [PRIV_LEN-1:0]    match_priv_o;
    logic                   priv_lvl_mode_o;
    logic                   iaddr_filter_o;
    logic [XLEN-1:0]        upper_iaddr_o;
    logic [XLEN-1:0]        lower_iaddr_o;
    logic [XLEN-1:0]        match_iaddr_o;
    logic                   iaddr_mode_o;
    logic                   trace_enable_o;
    logic                   trace_activated_o;
    logic                   nocontext_o;
    logic                   notime_o;
    logic                   encoder_mode_o;
    ioptions_s              configuration_o;
    logic                   lossless_trace_o;
    logic                   shallow_trace_o;
    logic                   clk_gated_o;
    logic                   pready_o;
    logic [31:0]            prdata_o;

    // testing only outputs
    logic                   expected_cause_filter;
    logic [XLEN-1:0]        expected_upper_cause;
    logic [XLEN-1:0]        expected_lower_cause;
    logic [XLEN-1:0]        expected_match_cause;
    logic                   expected_cause_mode;
    logic                   expected_tvec_filter;
    logic [XLEN-1:0]        expected_upper_tvec;
    logic [XLEN-1:0]        expected_lower_tvec;
    logic [XLEN-1:0]        expected_match_tvec;
    logic                   expected_tvec_mode;
    logic                   expected_tval_filter;
    logic [XLEN-1:0]        expected_upper_tval;
    logic [XLEN-1:0]        expected_lower_tval;
    logic [XLEN-1:0]        expected_match_tval;
    logic                   expected_tval_mode;
    logic                   expected_priv_lvl_filter;
    logic [PRIV_LEN-1:0]    expected_upper_priv;
    logic [PRIV_LEN-1:0]    expected_lower_priv;
    logic [PRIV_LEN-1:0]    expected_match_priv;
    logic                   expected_priv_lvl_mode;
    logic                   expected_iaddr_filter;
    logic [XLEN-1:0]        expected_upper_iaddr;
    logic [XLEN-1:0]        expected_lower_iaddr;
    logic [XLEN-1:0]        expected_match_iaddr;
    logic                   expected_iaddr_mode;
    logic                   expected_trace_enable;
    logic                   expected_trace_activated;
    logic                   expected_nocontext;
    logic                   expected_notime;
    logic                   expected_encoder_mode;
    ioptions_s              expected_configuration;
    logic                   expected_lossless_trace;
    logic                   expected_shallow_trace;
    logic                   expected_clk_gated;
    logic                   expected_pready;
    logic [31:0]            expected_prdata;

    // iteration variable
    logic [31:0] i;

    // DUT instantiation
    te_reg DUT(
        .clk_i               (clk),
        .rst_ni              (reset),
        .trace_req_off_i     (trace_req_off_i),
        .trace_req_on_i      (trace_req_on_i),
        .encapsulator_ready_i(encapsulator_ready_i),
        .cause_filter_o      (cause_filter_o),
        .upper_cause_o       (upper_cause_o),
        .lower_cause_o       (lower_cause_o),
        .match_cause_o       (match_cause_o),
        .cause_mode_o        (cause_mode_o),
        .tvec_filter_o       (tvec_filter_o),
        .upper_tvec_o        (upper_tvec_o),
        .lower_tvec_o        (lower_tvec_o),
        .match_tvec_o        (match_tvec_o),
        .tvec_mode_o         (tvec_mode_o),
        .tval_filter_o       (tval_filter_o),
        .upper_tval_o        (upper_tval_o),
        .lower_tval_o        (lower_tval_o),
        .match_tval_o        (match_tval_o),
        .tval_mode_o         (tval_mode_o),
        .priv_lvl_filter_o   (priv_lvl_filter_o),
        .upper_priv_o        (upper_priv_o),
        .lower_priv_o        (lower_priv_o),
        .match_priv_o        (match_priv_o),
        .priv_lvl_mode_o     (priv_lvl_mode_o),
        .iaddr_filter_o      (iaddr_filter_o),
        .upper_iaddr_o       (upper_iaddr_o),
        .lower_iaddr_o       (lower_iaddr_o),
        .match_iaddr_o       (match_iaddr_o),
        .iaddr_mode_o        (iaddr_mode_o),
        .trace_enable_o      (trace_enable_o),
        .trace_activated_o   (trace_activated_o),
        .nocontext_o         (nocontext_o),
        .notime_o            (notime_o),
        .encoder_mode_o      (encoder_mode_o),
        .configuration_o     (configuration_o),
        .lossless_trace_o    (lossless_trace_o),
        .shallow_trace_o     (shallow_trace_o),
        .clk_gated_o         (clk_gated_o),
        .paddr_i             (paddr_i),
        .pwrite_i            (pwrite_i),
        .psel_i              (psel_i),
        .penable_i           (penable_i),
        .pwdata_i            (pwdata_i),
        .pready_o            (pready_o),
        .prdata_o            (prdata_o)
    );

    logic [724:0] test_vector[1000:0];
    //    length of line   # of lines

    initial begin // reading test vector
        $readmemb("./tb/testvectors/tv_te_reg.txt", test_vector);
        i = 0;
        reset = 0; #10;
        reset = 1;
    end

    always @(posedge clk) begin // on posedge we get expected output
        {
            trace_req_off_i,
            trace_req_on_i,
            encapsulator_ready_i,
            paddr_i,
            pwrite_i,
            psel_i,
            penable_i,
            pwdata_i,
            expected_cause_filter,
            expected_upper_cause,
            expected_lower_cause,
            expected_match_cause,
            expected_cause_mode,
            expected_tvec_filter,
            expected_upper_tvec,
            expected_lower_tvec,
            expected_match_tvec,
            expected_tvec_mode,
            expected_tval_filter,
            expected_upper_tval,
            expected_lower_tval,
            expected_match_tval,
            expected_tval_mode,
            expected_priv_lvl_filter,
            expected_upper_priv,
            expected_lower_priv,
            expected_match_priv,
            expected_priv_lvl_mode,
            expected_iaddr_filter,
            expected_upper_iaddr,
            expected_lower_iaddr,
            expected_match_iaddr,
            expected_iaddr_mode,
            expected_trace_enable,
            expected_trace_activated,
            expected_nocontext,
            expected_notime,
            expected_encoder_mode,
            expected_configuration,
            expected_lossless_trace,
            expected_shallow_trace,
            expected_clk_gated,
            expected_pready,
            expected_prdata
        } = test_vector[i]; #10; 
    end

    always @(negedge clk) begin// on negedge we compare the expected result with the actual one
        // upper_tvec
        if (expected_upper_tvec !== upper_tvec_o) begin
            $display("Wrong upper_tvec: %b!=%b", expected_upper_tvec, upper_tvec_o);
        end
        // lossless_trace
        if (expected_lossless_trace !== lossless_trace_o) begin
            $display("Wrong lossless_trace: %b!=%b", expected_lossless_trace, lossless_trace_o);
        end
        // upper_priv
        if (expected_upper_priv !== upper_priv_o) begin
            $display("Wrong upper_priv: %b!=%b", expected_upper_priv, upper_priv_o);
        end
        // lower_priv
        if (expected_lower_priv !== lower_priv_o) begin
            $display("Wrong lower_priv: %b!=%b", expected_lower_priv, lower_priv_o);
        end
        // prdata_o
        if (expected_prdata !== prdata_o) begin
            $display("Wrong prdata_o: %b!=%b", expected_prdata, prdata_o);
        end

        // index increase
        i = i + 1;
    end

    always begin
        clk <= 1; #5;
        clk <= 0; #5;
    end

endmodule