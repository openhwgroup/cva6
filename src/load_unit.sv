// Author: Florian Zaruba, ETH Zurich
// Date: 22.05.2017
// Description: Load Unit, takes care of all load requests
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

// ---------------
// D$ Tag Status
// ---------------
`define WAIT_TRANSLATION  2'b00
`define VALID_TRANSLATION 2'b01
`define ABORT_TRANSLATION 2'b10
`define NOT_IMPL          2'b11

module load_unit (
    input  logic                     clk_i,    // Clock
    input  logic                     rst_ni,   // Asynchronous reset active low
    input  logic                     flush_i,
    // load unit input port
    input  fu_op                     operator_i,
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,
    input  logic                     valid_i,
    input  logic [63:0]              vaddr_i,
    input  logic [7:0]               be_i,
    // load unit output port
    output logic                     valid_o,
    output logic                     ready_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o,
    output exception                 ex_o,
    // MMU -> Address Translation
    output logic                     translation_req_o,   // request address translation
    output logic [63:0]              vaddr_o,             // virtual address out
    input  logic [63:0]              paddr_i,             // physical address in
    input  logic                     translation_valid_i,
    input  exception                 ex_i,
    // address checker
    output logic [11:0]              page_offset_o,
    input  logic                     page_offset_matches_i,
    // memory interface
    output logic [63:0]              address_o,
    output logic [63:0]              data_wdata_o,
    output logic                     data_req_o,
    output logic                     data_we_o,
    output logic [7:0]               data_be_o,
    output logic [1:0]               data_tag_status_o,
    input  logic                     data_gnt_i,
    input  logic                     data_rvalid_i,
    input  logic [63:0]              data_rdata_i
);
    enum logic [2:0] {IDLE, WAIT_GNT, SEND_TAG, ABORT_TRANSLATION, WAIT_FLUSH} NS, CS;

    typedef struct packed {
        logic [TRANS_ID_BITS-1:0] trans_id;
        logic [2:0]               address_offset;
        fu_t                      operator;
    } rvalid_entry_t;

    rvalid_entry_t in_data;
    logic          push;
    rvalid_entry_t out_data;
    logic          pop;
    logic          empty;

    logic [63:0] paddr_n, paddr_q;
    // page offset is defined as the lower 12 bits
    assign page_offset_o = vaddr_i[11:0];
    // feed-through the virtual address
    assign vaddr_o = vaddr_i;
    // this is a read-only interface so set the write enable to 0
    assign data_we_o = 1'b0;
    assign in_data = {trans_id_i, vaddr_i[2:0], operator_i};
    // output address
    // we can now output the lower 12 bit as the index to the cache
    assign address_o [11:0] = vaddr_i[11:0];
    // translation from last cycle
    assign address_o[63:12] =  paddr_q[63:12];
    // ---------------
    // Load Control
    // ---------------
    always_comb begin : load_controll
        // default assignments
        NS                = CS;
        paddr_n           = paddr_q;
        translation_req_o = 1'b0;
        ready_o           = 1'b1;
        data_req_o        = 1'b0;
        data_tag_status_o = `WAIT_TRANSLATION;
        push              = 1'b0;
        data_be_o         = be_i;
        ex_o              = ex_i;

        case (CS)
            IDLE: begin
                // we've got a new load request
                if (valid_i) begin
                    // start the translation process even though we do not know if the addresses match
                    // this should ease timing
                    translation_req_o = 1'b1;
                    // check if the page offset matches with a store, if it does then stall and wait
                    if (!page_offset_matches_i) begin
                        // make a load request to memory
                        data_req_o        = 1'b1;
                        // the translation request we got is valid
                        if (translation_valid_i) begin
                            // save the physical address for the next cycle
                            paddr_n = paddr_i;
                            // we got no data grant so wait for the grant before sending the tag
                            if (!data_gnt_i) begin
                                NS = WAIT_GNT;
                                ready_o = 1'b0;
                            end else begin
                                // put the request in the queue
                                push    = 1'b1;
                                // we got a grant so we can send the tag in the next cycle
                                NS = SEND_TAG;
                            end
                        // we got a TLB miss
                        end else begin
                            // we need to abort the translation and let the PTW walker fix the TLB miss
                            NS = ABORT_TRANSLATION;
                            ready_o = 1'b0;
                        end
                    end else begin
                        // stall and wait for the store-buffer to drain
                        ready_o = 1'b0;
                    end
                end
            end
            // we are here because of a TLB miss
            ABORT_TRANSLATION: begin
                // we are not ready here
                ready_o = 1'b0;
                // send an abort signal
                data_tag_status_o = `ABORT_TRANSLATION;
                // wait for the translation to become valid and redo the request
                if (translation_valid_i) begin
                    // we have a valid translation so tell the cache it should wait for it on the next cycle
                    data_tag_status_o = `WAIT_TRANSLATION;
                    // if the request is still here, do the load
                    if (valid_i) begin

                        data_req_o = 1'b1;
                        paddr_n    = paddr_i;

                        if (!data_gnt_i) begin
                            NS = WAIT_GNT;
                            ready_o = 1'b0;
                        end else begin
                            // here we are ready to accept a new request
                            ready_o = 1'b1;
                            // put the request in the queue
                            push    = 1'b1;
                            // we got a grant so we can send the tag in the next cycle
                            NS = SEND_TAG;
                        end
                    end
                end
            end

            WAIT_GNT: begin
                // we are waiting for the grant so we are not ready to accept anything new
                ready_o = 1'b0;
                // keep the request up
                data_req_o = 1'b1;
                // we finally got a data grant
                if (data_gnt_i) begin
                    // so we send the tag in the next cycle
                    NS = SEND_TAG;
                    // we store this grant in our queue
                    push = 1'b1;
                    // plus: we can accept a new request
                    ready_o = 1'b1;
                end
                // otherwise we keep waiting on our grant
            end

            SEND_TAG: begin
                ready_o = 1'b1;
                // if we are sending our tag we are able to process a new request
                data_tag_status_o = `VALID_TRANSLATION;
                // -------------
                // New Request
                // -------------
                // we can make a new request if we got one
                if (valid_i) begin
                    // do another address translation
                    translation_req_o = 1'b1;
                        if(!page_offset_matches_i) begin
                            // make a load request to memory
                            data_req_o        = 1'b1;
                            // the translation request we got is valid
                            if (translation_valid_i) begin
                                // save the physical address for the next cycle
                                paddr_n = paddr_i;
                                // we got no data grant so wait for the grant before sending the tag
                                if (!data_gnt_i) begin
                                    NS = WAIT_GNT;
                                    ready_o = 1'b0;
                                end else begin
                                    // put the request in the queue
                                    push    = 1'b1;
                                    // we got a grant so we can send the tag in the next cycle
                                    NS = SEND_TAG;
                                end
                            // we got a TLB miss
                            end else begin
                                // we need to abort the translation and let the PTW walker fix the TLB miss
                                NS = ABORT_TRANSLATION;
                                ready_o = 1'b0;
                            end
                    // page offset mis-match -> go back to idle
                    end else begin
                        NS = IDLE;
                    end
                end else begin
                    NS = IDLE;
                end
            end

            WAIT_FLUSH: begin
                ready_o = 1'b0;
                // we got all outstanding requests
                if (empty) begin
                    ready_o = 1'b1;
                    NS = IDLE;
                end
            end

        endcase
        // -----------------
        // Access Exception
        // -----------------
        // we've got an exception
        if (valid_i && ex_i.valid) begin
            // clear the request
            data_req_o  = 1'b0;
            // we are ready
            ready_o     = 1'b1;
            // do not push this request
            push        = 1'b0;
        end
        // if we just flushed and the queue is not empty or we are getting an rvalid this cycle wait in an extra stage
        if (flush_i && (!empty || data_rvalid_i)) begin
            NS = WAIT_FLUSH;
        end
    end

    // decoupled rvalid process
    always_comb begin : rvalid_output
        pop     = 1'b0;
        valid_o = 1'b0;
        // we got an rvalid and are currently not flushing
        if (data_rvalid_i && CS != WAIT_FLUSH) begin
            pop     = 1'b1;
            valid_o = 1'b1;
        end
        // pass through an exception
        if (valid_i && ex_i.valid) begin
            valid_o = 1'b1;
        end
    end

    // output the queue data directly, the valid signal is set corresponding to the process above
    assign trans_id_o = out_data.trans_id;

    // latch physical address
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            CS      <= IDLE;
            paddr_q <= '0;
        end else begin
            CS      <= NS;
            paddr_q <= paddr_n;
        end
    end

    // --------------
    // Rvalid FIFO
    // --------------
    // we can have two outstanding requests, hence we need to elements in the FIFO
    fifo #(
        .dtype            ( rvalid_entry_t   ),
        .DEPTH            ( 2                )
    )
    fifo_i (
        .full_o           (                  ), // we can ignore the full signal, the FIFO will never overflow
        .empty_o          ( empty            ),
        .single_element_o (                  ), // we don't care about the single element either

        .data_i           ( in_data          ),
        .push_i           ( push             ),
        .data_o           ( out_data         ),
        .pop_i            ( pop              ),
        .*
    );

    // ---------------
    // Sign Extend
    // ---------------
    logic [63:0] rdata_d_ext; // sign extension for double words, actually only misaligned assembly
    logic [63:0] rdata_w_ext; // sign extension for words
    logic [63:0] rdata_h_ext; // sign extension for half words
    logic [63:0] rdata_b_ext; // sign extension for bytes

    // double words
    always_comb begin : sign_extend_double_word
        rdata_d_ext = data_rdata_i[63:0];
    end

      // sign extension for words
    always_comb begin : sign_extend_word
        case (out_data.address_offset)
            default: rdata_w_ext = (out_data.operator == LW) ? {{32{data_rdata_i[31]}}, data_rdata_i[31:0]}  : {32'h0, data_rdata_i[31:0]};
            3'b001:  rdata_w_ext = (out_data.operator == LW) ? {{32{data_rdata_i[39]}}, data_rdata_i[39:8]}  : {32'h0, data_rdata_i[39:8]};
            3'b010:  rdata_w_ext = (out_data.operator == LW) ? {{32{data_rdata_i[47]}}, data_rdata_i[47:16]} : {32'h0, data_rdata_i[47:16]};
            3'b011:  rdata_w_ext = (out_data.operator == LW) ? {{32{data_rdata_i[55]}}, data_rdata_i[55:24]} : {32'h0, data_rdata_i[55:24]};
            3'b100:  rdata_w_ext = (out_data.operator == LW) ? {{32{data_rdata_i[63]}}, data_rdata_i[63:32]} : {32'h0, data_rdata_i[63:32]};
        endcase
    end

    // sign extension for half words
    always_comb begin : sign_extend_half_word
        case (out_data.address_offset)
            default: rdata_h_ext = (out_data.operator == LH) ? {{48{data_rdata_i[15]}}, data_rdata_i[15:0]}  : {48'h0, data_rdata_i[15:0]};
            3'b001:  rdata_h_ext = (out_data.operator == LH) ? {{48{data_rdata_i[23]}}, data_rdata_i[23:8]}  : {48'h0, data_rdata_i[23:8]};
            3'b010:  rdata_h_ext = (out_data.operator == LH) ? {{48{data_rdata_i[31]}}, data_rdata_i[31:16]} : {48'h0, data_rdata_i[31:16]};
            3'b011:  rdata_h_ext = (out_data.operator == LH) ? {{48{data_rdata_i[39]}}, data_rdata_i[39:24]} : {48'h0, data_rdata_i[39:24]};
            3'b100:  rdata_h_ext = (out_data.operator == LH) ? {{48{data_rdata_i[47]}}, data_rdata_i[47:32]} : {48'h0, data_rdata_i[47:32]};
            3'b101:  rdata_h_ext = (out_data.operator == LH) ? {{48{data_rdata_i[55]}}, data_rdata_i[55:40]} : {48'h0, data_rdata_i[55:40]};
            3'b110:  rdata_h_ext = (out_data.operator == LH) ? {{48{data_rdata_i[63]}}, data_rdata_i[63:48]} : {48'h0, data_rdata_i[63:48]};
        endcase
    end

    always_comb begin : sign_extend_byte
        case (out_data.address_offset)
            default: rdata_b_ext = (out_data.operator == LB) ? {{56{data_rdata_i[7]}},  data_rdata_i[7:0]}   : {56'h0, data_rdata_i[7:0]};
            3'b001:  rdata_b_ext = (out_data.operator == LB) ? {{56{data_rdata_i[15]}}, data_rdata_i[15:8]}  : {56'h0, data_rdata_i[15:8]};
            3'b010:  rdata_b_ext = (out_data.operator == LB) ? {{56{data_rdata_i[23]}}, data_rdata_i[23:16]} : {56'h0, data_rdata_i[23:16]};
            3'b011:  rdata_b_ext = (out_data.operator == LB) ? {{56{data_rdata_i[31]}}, data_rdata_i[31:24]} : {56'h0, data_rdata_i[31:24]};
            3'b100:  rdata_b_ext = (out_data.operator == LB) ? {{56{data_rdata_i[39]}}, data_rdata_i[39:32]} : {56'h0, data_rdata_i[39:32]};
            3'b101:  rdata_b_ext = (out_data.operator == LB) ? {{56{data_rdata_i[47]}}, data_rdata_i[47:40]} : {56'h0, data_rdata_i[47:40]};
            3'b110:  rdata_b_ext = (out_data.operator == LB) ? {{56{data_rdata_i[55]}}, data_rdata_i[55:48]} : {56'h0, data_rdata_i[55:48]};
            3'b111:  rdata_b_ext = (out_data.operator == LB) ? {{56{data_rdata_i[63]}}, data_rdata_i[63:56]} : {56'h0, data_rdata_i[63:56]};
        endcase
    end

    always_comb begin
        case (out_data.operator)
            LW, LWU:       result_o = rdata_w_ext;
            LH, LHU:       result_o = rdata_h_ext;
            LB, LBU:       result_o = rdata_b_ext;
            default:       result_o = rdata_d_ext;
        endcase
    end

endmodule