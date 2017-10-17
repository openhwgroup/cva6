// Author: Florian Zaruba, ETH Zurich
// Date: 13.10.2017
// Description: This module handles the AXI transactions
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
import nbdcache_pkg::*;

module axi_adapter #(
    parameter int unsigned CACHE_LINE_WIDTH  = 256,
    parameter int unsigned AXI_ID_WIDTH      = 10,
    parameter int unsigned AXI_USER_WIDTH    = 10
)(
    input  logic                                        clk_i,  // Clock
    input  logic                                        rst_ni, // Asynchronous reset active low

    input  logic                                        req_i,
    input  req_t                                        type_i,
    output logic                                        gnt_o,
    input  logic [63:0]                                 addr_i,
    input  logic                                        we_i,
    input  logic [(CACHE_LINE_WIDTH/64)-1:0][63:0]      wdata_i,
    input  logic [(CACHE_LINE_WIDTH/64)-1:0][7:0]       be_i,
    input  logic [AXI_ID_WIDTH-1:0]                     id_i,
    // read port
    output logic                                        valid_o,
    output logic [127:0]                                rdata_o,
    output logic [AXI_ID_WIDTH-1:0]                     id_o,
    // critical word - read port
    output logic [63:0]                                 critical_word_o,
    output logic                                        critical_word_valid,
    // AXI port
    AXI_BUS.Master                                      axi
);
    localparam BURST_SIZE = CACHE_LINE_WIDTH/64;

    enum logic [3:0] {
        IDLE, WAIT_B_VALID, WAIT_AW_READY, WAIT_LAST_W_READY, WAIT_LAST_W_READY_AW_READY, WAIT_AW_READY_BURST,
        WAIT_R_VALID, WAIT_R_VALID_MULTIPLE, COMPLETE_READ
    } state_q, state_d;

    // counter for AXI transfers
    logic [$clog2(CACHE_LINE_WIDTH/64)-1:0] cnt_d, cnt_q;
    logic [(CACHE_LINE_WIDTH/64)-1:0][63:0] cache_line_d, cache_line_q;
    // save the address for a read, as we allow for non-cacheline aligned accesses
    logic [$clog2(CACHE_LINE_WIDTH/64)-1:0]  addr_offset_d, addr_offset_q;

    always_comb begin : axi_fsm
        // Default assignments
        axi.aw_valid  = 1'b0;
        axi.aw_addr   = addr_i;
        axi.aw_prot   = 3'b0;
        axi.aw_region = 4'b0;
        axi.aw_len    = 8'b0;
        axi.aw_size   = 3'b011; // 8 bytes
        axi.aw_burst  = 2'b01;  // incremental transfer
        axi.aw_lock   = 1'b0;
        axi.aw_cache  = 4'b0;
        axi.aw_qos    = 4'b0;
        axi.aw_id     = id_i;
        axi.aw_user   = '0;

        axi.ar_valid  = 1'b0;
        axi.ar_addr   = addr_i;
        axi.ar_prot   = 3'b0;
        axi.ar_region = 4'b0;
        axi.ar_len    = 8'b0;
        axi.ar_size   = 3'b011; // 8 bytes
        axi.ar_burst  = 2'b10;  // wrapping transfer
        axi.ar_lock   = 1'b0;
        axi.ar_cache  = 4'b0;
        axi.ar_qos    = 4'b0;
        axi.ar_id     = id_i;
        axi.ar_user   = '0;

        axi.w_valid   = 1'b0;
        axi.w_data    = wdata_i[0];
        axi.w_strb    = be_i[0];
        axi.w_user    = '0;
        axi.w_last    = 1'b0;

        axi.b_ready   = 1'b0;
        axi.r_ready   = 1'b0;

        gnt_o         = 1'b0;
        valid_o       = 1'b0;
        id_o          = axi.r_id;

        // rdata_o   = axi.r_data;
        critical_word_o       = axi.r_data;
        critical_word_valid   = 1'b0;

        state_d       = state_q;
        cnt_d         = cnt_q;
        cache_line_d  = cache_line_q;
        addr_offset_d = addr_offset_q;

        case (state_q)

            IDLE: begin
                cnt_d = '0;
                // we have an incoming request
                if (req_i) begin
                    // is this a read or write?
                    // write
                    if (we_i) begin
                        // the data is valid
                        axi.aw_valid = 1'b1;
                        axi.w_valid  = 1'b1;
                        // its a single write
                        if (type_i == SINGLE_REQ) begin
                            // single req can be granted here
                            gnt_o = axi.aw_ready & axi.w_ready;

                            case ({axi.aw_ready, axi.w_ready})
                                2'b11: state_d = WAIT_B_VALID;
                                2'b01: state_d = WAIT_AW_READY;
                                2'b10: state_d = WAIT_LAST_W_READY;
                                default: state_d = IDLE;
                            endcase
                        // its a request for the whole cache line
                        end else begin
                            axi.aw_len = BURST_SIZE; // number of bursts to do
                            axi.w_last = 1'b0;
                            axi.w_data = wdata_i[0];
                            axi.w_strb = be_i[0];

                            if (axi.w_ready)
                                cnt_d = BURST_SIZE - 1;
                            else
                                cnt_d = BURST_SIZE;

                            case ({axi.aw_ready, axi.w_ready})
                                2'b11: state_d = WAIT_LAST_W_READY;
                                2'b01: state_d = WAIT_LAST_W_READY_AW_READY;
                                2'b10: state_d = WAIT_LAST_W_READY;
                                default:;
                            endcase
                        end
                    // read
                    end else begin

                        axi.ar_valid = 1'b1;
                        gnt_o = axi.ar_ready;

                        if (type_i != SINGLE_REQ) begin
                            axi.ar_len = CACHE_LINE_WIDTH/64;
                            cnt_d = CACHE_LINE_WIDTH/64 - 1;
                        end

                        if (axi.ar_ready) begin
                            state_d = (type_i == SINGLE_REQ) ? WAIT_R_VALID : WAIT_R_VALID_MULTIPLE;
                            addr_offset_d = addr_i[$clog2(CACHE_LINE_WIDTH/64)-1:0];
                        end
                    end
                end
            end

            // ~> from single write, write request has already been granted
            WAIT_AW_READY: begin
                axi.aw_valid = 1'b1;
                axi.aw_len   = 8'b0;

                if (axi.aw_ready)
                    state_d = WAIT_B_VALID;

            end

            // ~> we need to wait for an aw_ready and there is at least one outstanding write
            WAIT_LAST_W_READY_AW_READY: begin

                axi.w_valid  = 1'b1;
                axi.w_last   = (cnt_q == '0) ? 1'b1 : 1'b0;
                axi.w_data   = wdata_i[BURST_SIZE-cnt_q];
                axi.w_strb   = be_i[BURST_SIZE-cnt_q];

                axi.aw_valid = 1'b1;
                // we are here because we want to write a cache line
                axi.aw_len   = CACHE_LINE_WIDTH/64;
                // we got an aw_ready
                case ({axi.aw_ready, axi.w_ready})
                    // we got an aw ready
                    2'b01: begin
                        // are there any outstanding transactions?
                        if (cnt_q == 0)
                            state_d = WAIT_AW_READY_BURST;
                        else // yes, so reduce the count and stay here
                            cnt_d = cnt_q - 1;
                    end
                    2'b10: state_d = WAIT_LAST_W_READY;
                    2'b11: begin
                        // we are finished
                        if (cnt_q == 0) begin
                            state_d = WAIT_B_VALID;
                            gnt_o = 1'b1;
                        // there are outstanding transactions
                        end else begin
                            state_d = WAIT_LAST_W_READY;
                            cnt_d = cnt_q - 1;
                        end
                    end
                    default:;
               endcase

            end

            // ~> all data has already been sent, we are only waiting for the aw_ready
            WAIT_AW_READY_BURST: begin
                axi.aw_valid = 1'b1;
                axi.aw_len   = CACHE_LINE_WIDTH/64;

                if (axi.aw_ready) begin
                    state_d = WAIT_B_VALID;
                    gnt_o = 1'b1;
                end
            end

            // ~> from write, there is an outstanding write
            WAIT_LAST_W_READY: begin
                axi.w_valid = 1'b1;
                axi.w_data  = wdata_i[BURST_SIZE-cnt_q];
                axi.w_strb  = be_i[BURST_SIZE-cnt_q];

                // this is the last write
                axi.w_last  = (cnt_q == '0) ? 1'b1 : 1'b0;
                gnt_o = (cnt_q == '0);

                if (axi.w_ready) begin
                    // last write -> go to WAIT_B_VALID
                    if (cnt_q == '0)
                        state_d = WAIT_B_VALID;
                    else
                        cnt_d = cnt_q - 1;
                end
            end

            // ~> finish write transaction
            WAIT_B_VALID: begin
                axi.b_ready = 1'b1;
                id_o = axi.b_id;

                // Write is valid
                if (axi.b_valid) begin
                    state_d = IDLE;
                    valid_o = 1'b1;
                end
            end

            // ~> cacheline read, single read
            WAIT_R_VALID_MULTIPLE, WAIT_R_VALID: begin
                // reads are always wrapping here
                axi.r_ready = 1'b1;
                // this is the first read a.k.a the critical word
                if (axi.r_valid) begin
                    // this is the first word of a cacheline read
                    if (state_q == WAIT_R_VALID_MULTIPLE) begin
                        critical_word_valid = 1'b1;
                        critical_word_o     = axi.r_data;
                    end
                    // this is the last read
                    if (axi.r_last) begin
                        state_d = COMPLETE_READ;
                    end

                    // save the word
                    if (state_q == WAIT_R_VALID_MULTIPLE)
                        cache_line_d[addr_offset_q + cnt_q] = axi.r_data;
                    else
                        cache_line_d[0] = axi.r_data;
                end
            end
            // ~> read is complete
            COMPLETE_READ: begin
                valid_o = 1'b1;
                state_d = IDLE;
            end
        endcase
    end

    // ----------------
    // Registers
    // ----------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q       <= IDLE;
            cnt_q         <= '0;
            cache_line_q  <= '0;
            addr_offset_q <= '0;
        end else begin
            state_q       <= state_d;
            cnt_q         <= cnt_d;
            cache_line_q  <= cache_line_d;
            addr_offset_q <= addr_offset_d;
        end
    end

endmodule
