// Author: Florian Zaruba, ETH Zurich
// Date: 22.05.2017
// Description: Store Unit, takes care of all store requests
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.

import ariane_pkg::*;

module store_unit (
    input  logic                     clk_i,    // Clock
    input  logic                     rst_ni,  // Asynchronous reset active low
    input  logic                     flush_i,
    output logic                     no_st_pending_o,
    // store unit input port
    input  logic                     valid_i,
    input  lsu_ctrl_t                lsu_ctrl_i,
    output logic                     pop_st_o,
    input  logic                     commit_i,
    output logic                     commit_ready_o,

    // store unit output port
    output logic                     valid_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o,
    output exception                 ex_o,
    // MMU -> Address Translation
    output logic                     translation_req_o, // request address translation
    output logic [63:0]              vaddr_o,           // virtual address out
    input  logic [63:0]              paddr_i,           // physical address in
    input  exception                 ex_i,
    input  logic                     dtlb_hit_i,       // will be one in the same cycle translation_req was asserted if it hits
    // address checker
    input  logic [11:0]              page_offset_i,
    output logic                     page_offset_matches_o,
    // D$ interface
    output logic [11:0]              address_index_o,
    output logic [43:0]              address_tag_o,
    output logic [63:0]              data_wdata_o,
    output logic                     data_req_o,
    output logic                     data_we_o,
    output logic [7:0]               data_be_o,
    output logic                     kill_req_o,
    output logic                     tag_valid_o,
    input  logic                     data_gnt_i,
    input  logic                     data_rvalid_i
);
    assign result_o = 64'b0;

    enum logic [1:0] {IDLE, VALID_STORE, WAIT_TRANSLATION, WAIT_STORE_READY} NS, CS;

    // store buffer control signals
    logic                    st_ready;
    logic                    st_valid;

    // keep the data and the byte enable for the second cycle (after address translation)
    logic [63:0]              st_data_n, st_data_q;
    logic [7:0]               st_be_n,   st_be_q;
    logic [TRANS_ID_BITS-1:0] trans_id_n, trans_id_q;

    // output assignments
    assign vaddr_o    = lsu_ctrl_i.vaddr; // virtual address
    assign trans_id_o = trans_id_q; // transaction id from previous cycle

    always_comb begin : store_control
        translation_req_o = 1'b0;
        valid_o           = 1'b0;
        st_valid          = 1'b0;
        pop_st_o          = 1'b0;
        ex_o              = ex_i;
        trans_id_n        = lsu_ctrl_i.trans_id;
        NS                = CS;

        case (CS)
            // we got a valid store
            IDLE: begin
                if (valid_i) begin

                    NS = VALID_STORE;
                    translation_req_o = 1'b1;
                    pop_st_o = 1'b1;
                    // check if translation was valid and we have space in the store buffer
                    // otherwise simply stall
                    if (!dtlb_hit_i) begin
                        NS = WAIT_TRANSLATION;
                        pop_st_o = 1'b0;
                    end

                    if (!st_ready) begin
                        NS = WAIT_STORE_READY;
                        pop_st_o = 1'b0;
                    end
                end
            end

            VALID_STORE: begin
                valid_o  = 1'b1;
                // post this store to the store buffer if we are not flushing
                if (!flush_i)
                    st_valid = 1'b1;

                // we have another request
                if (valid_i) begin

                    translation_req_o = 1'b1;
                    NS = VALID_STORE;
                        pop_st_o = 1'b1;

                    if (!dtlb_hit_i) begin
                        NS = WAIT_TRANSLATION;
                        pop_st_o = 1'b0;
                    end

                    if (!st_ready) begin
                        pop_st_o = 1'b0;
                        NS = WAIT_STORE_READY;
                    end
                // if we do not have another request go back to idle
                end else begin
                    NS = IDLE;
                end
            end

            // the store queue is currently full
            WAIT_STORE_READY: begin
                // keep the translation request high
                translation_req_o = 1'b1;

                if (st_ready && dtlb_hit_i) begin
                    NS = IDLE;
                end
            end

            // we didn't receive a valid translation, wait for one
            // but we know that the store queue is not full as we could only have landed here if
            // it wasn't full
            WAIT_TRANSLATION: begin
                translation_req_o = 1'b1;

                if (dtlb_hit_i) begin
                    NS = IDLE;
                end
            end
        endcase

        // -----------------
        // Access Exception
        // -----------------
        // we got an address translation exception (access rights, misaligned or page fault)
        if (ex_i.valid && (CS != IDLE)) begin
            // the only difference is that we do not want to store this request
            st_valid = 1'b0;
            NS       = IDLE;
            valid_o  = 1'b1;
        end

        if (flush_i)
            NS = IDLE;
    end

    // -----------
    // Re-aligner
    // -----------
    // re-align the write data to comply with the address offset
    always_comb begin
        st_be_n   = lsu_ctrl_i.be;
        st_data_n = lsu_ctrl_i.data;
        case (lsu_ctrl_i.vaddr[2:0])
            3'b000: st_data_n = lsu_ctrl_i.data;
            3'b001: st_data_n = {lsu_ctrl_i.data[55:0], lsu_ctrl_i.data[63:56]};
            3'b010: st_data_n = {lsu_ctrl_i.data[47:0], lsu_ctrl_i.data[63:48]};
            3'b011: st_data_n = {lsu_ctrl_i.data[39:0], lsu_ctrl_i.data[63:40]};
            3'b100: st_data_n = {lsu_ctrl_i.data[31:0], lsu_ctrl_i.data[63:32]};
            3'b101: st_data_n = {lsu_ctrl_i.data[23:0], lsu_ctrl_i.data[63:24]};
            3'b110: st_data_n = {lsu_ctrl_i.data[15:0], lsu_ctrl_i.data[63:16]};
            3'b111: st_data_n = {lsu_ctrl_i.data[7:0],  lsu_ctrl_i.data[63:8]};
        endcase
    end
    // ---------------
    // Store Queue
    // ---------------
    store_buffer store_buffer_i (
        // store queue write port
        .valid_i           ( st_valid            ),
        .data_i            ( st_data_q           ),
        .be_i              ( st_be_q             ),
        // store buffer out
        .ready_o           ( st_ready            ),
        .*
    );
    // ---------------
    // Registers
    // ---------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            CS         <= IDLE;
            st_be_q    <= '0;
            st_data_q  <= '0;
            trans_id_q <= '0;
        end else begin
            CS         <= NS;
            st_be_q    <= st_be_n;
            st_data_q  <= st_data_n;
            trans_id_q <= trans_id_n;
        end
    end

endmodule
