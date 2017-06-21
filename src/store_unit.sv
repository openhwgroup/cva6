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
    input logic                      clk_i,    // Clock
    input logic                      rst_ni,  // Asynchronous reset active low
    input logic                      flush_i,
    output logic                     no_st_pending_o,
    // store unit input port
    input  fu_op                     operator_i,
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,
    input  logic                     valid_i,
    input  logic [63:0]              vaddr_i,
    input  logic [7:0]               be_i,
    input  logic [63:0]              data_i,
    input  logic                     commit_i,
    // store unit output port
    output logic                     valid_o,
    output logic                     ready_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o,
    output exception                 ex_o,
    // MMU -> Address Translation
    output logic                     translation_req_o, // request address translation
    output logic [63:0]              vaddr_o,           // virtual address out
    input  logic [63:0]              paddr_i,           // physical address in
    input  logic                     translation_valid_i,
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

    logic [63:0]             st_buffer_paddr;  // physical address for store
    logic [63:0]             st_data;          // aligned data to store buffer
    logic                    st_buffer_valid;
    // store buffer control signals
    logic                    st_ready;
    logic                    st_valid;

    // keep the data and the byte enable for the second cycle (after address translation)
    logic [63:0]              st_data_n, st_data_q;
    logic [7:0]               st_be_n,   st_be_q;
    logic [TRANS_ID_BITS-1:0] trans_id_n, trans_id_q;

    // output assignments
    assign vaddr_o    = vaddr_i; // virtual address
    assign trans_id_o = trans_id_q; // transaction id from previous cycle

    always_comb begin : store_control
        translation_req_o = 1'b0;
        ready_o           = 1'b1;
        valid_o           = 1'b0;
        st_valid          = 1'b0;
        ex_o              = ex_i;
        trans_id_n        = trans_id_i;
        NS                = CS;

        case (CS)
            // we got a valid store
            IDLE: begin
                if (valid_i) begin

                    NS                = VALID_STORE;
                    translation_req_o = 1'b1;

                    // check if translation was valid and we have space in the store buffer
                    // otherwise simply stall
                    if (!dtlb_hit_i) begin
                        NS = WAIT_TRANSLATION;
                    end

                    if (!st_ready) begin
                        NS = WAIT_STORE_READY;
                    end
                end
            end

            VALID_STORE: begin
                valid_o  = 1'b1;
                // post this store to the store buffer
                if (!flush_i)
                    st_valid = 1'b1;

                // we have another request
                if (valid_i) begin

                    translation_req_o = 1'b1;

                    if (!dtlb_hit_i) begin
                        NS = WAIT_TRANSLATION;
                    end

                    if (!st_ready) begin
                        NS = WAIT_STORE_READY;
                    end
                // if we do not have another request go back to idle
                end else begin
                    NS = IDLE;
                end
            end

            // the store queue is currently full
            WAIT_STORE_READY: begin
                ready_o           = 1'b0;
                // keep the translation request high
                translation_req_o = 1'b1;

                if (st_ready && dtlb_hit_i) begin
                    NS = VALID_STORE;
                end
            end

            // we didn't receive a valid translation, wait for one
            // but we know that the store queue is not full as we could only have landed here if
            // it wasn't full
            WAIT_TRANSLATION: begin
                ready_o = 1'b0;
                translation_req_o = 1'b1;

                if (dtlb_hit_i) begin
                    NS = VALID_STORE;
                end
            end
        endcase

        // -----------------
        // Access Exception
        // -----------------
        // we got an address translation exception (access rights, misaligned or page fault)
        if (ex_i.valid) begin
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
        st_be_n   = be_i;
        st_data_n = data_i;
        case (vaddr_i[2:0])
            3'b000: st_data_n = data_i;
            3'b001: st_data_n = {data_i[55:0], data_i[63:56]};
            3'b010: st_data_n = {data_i[47:0], data_i[63:48]};
            3'b011: st_data_n = {data_i[39:0], data_i[63:40]};
            3'b100: st_data_n = {data_i[31:0], data_i[63:32]};
            3'b101: st_data_n = {data_i[23:0], data_i[63:24]};
            3'b110: st_data_n = {data_i[15:0], data_i[63:16]};
            3'b111: st_data_n = {data_i[7:0],  data_i[63:8]};
        endcase
    end
    // ---------------
    // Store Queue
    // ---------------
    store_queue store_queue_i (
        // store queue write port
        .valid_i           ( st_valid            ),
        .data_i            ( st_data_q           ),
        .be_i              ( st_be_q             ),
        // store buffer out
        .paddr_o           ( st_buffer_paddr     ),
        .data_o            (                     ),
        .valid_o           ( st_buffer_valid     ),
        .be_o              (                     ),
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
    // ------------------
    // Address Checker
    // ------------------
    // The load should return the data stored by the most recent store to the
    // same physical address.  The most direct way to implement this is to
    // maintain physical addresses in the store buffer.

    // Of course, there are other micro-architectural techniques to accomplish
    // the same thing: you can interlock and wait for the store buffer to
    // drain if the load VA matches any store VA modulo the page size (i.e.
    // bits 11:0).  As a special case, it is correct to bypass if the full VA
    // matches, and no younger stores' VAs match in bits 11:0.
    //
    // checks if the requested load is in the store buffer
    // page offsets are virtually and physically the same
    always_comb begin : address_checker
        page_offset_matches_o = 1'b0;
        // check if the LSBs are identical and the entry is valid
        if ((vaddr_i[11:3] == st_buffer_paddr[11:3]) && st_buffer_valid) begin
            page_offset_matches_o = 1'b1;
        end

        if ((vaddr_i[11:3] == paddr_i[11:3]) && (CS == VALID_STORE)) begin
            page_offset_matches_o = 1'b1;
        end
    end

endmodule