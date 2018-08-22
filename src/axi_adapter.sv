/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:  axi_adapter.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   1.8.2018
 *
 * Description: Manages communication with the AXI Bus
 */
import std_cache_pkg::*;

module axi_adapter #(
        parameter int unsigned DATA_WIDTH          = 256,
        parameter logic        CRITICAL_WORD_FIRST = 0, // the AXI subsystem needs to support wrapping reads for this feature
        parameter int unsigned AXI_ID_WIDTH        = 10
    )(
    input  logic                                        clk_i,  // Clock
    input  logic                                        rst_ni, // Asynchronous reset active low

    input  logic                                        req_i,
    input  req_t                                        type_i,
    output logic                                        gnt_o,
    output logic [AXI_ID_WIDTH-1:0]                     gnt_id_o,
    input  logic [63:0]                                 addr_i,
    input  logic                                        we_i,
    input  logic [(DATA_WIDTH/64)-1:0][63:0]            wdata_i,
    input  logic [(DATA_WIDTH/64)-1:0][7:0]             be_i,
    input  logic [1:0]                                  size_i,
    input  logic [AXI_ID_WIDTH-1:0]                     id_i,
    // read port
    output logic                                        valid_o,
    output logic [(DATA_WIDTH/64)-1:0][63:0]            rdata_o,
    output logic [AXI_ID_WIDTH-1:0]                     id_o,
    // critical word - read port
    output logic [63:0]                                 critical_word_o,
    output logic                                        critical_word_valid_o,
    // AXI port
    AXI_BUS.Master                                      axi
);
    localparam BURST_SIZE = DATA_WIDTH/64-1;
    localparam ADDR_INDEX = ($clog2(DATA_WIDTH/64) > 0) ? $clog2(DATA_WIDTH/64) : 1;

    enum logic [3:0] {
        IDLE, WAIT_B_VALID, WAIT_AW_READY, WAIT_LAST_W_READY, WAIT_LAST_W_READY_AW_READY, WAIT_AW_READY_BURST,
        WAIT_R_VALID, WAIT_R_VALID_MULTIPLE, COMPLETE_READ
    } state_q, state_d;

    // counter for AXI transfers
    logic [ADDR_INDEX-1:0] cnt_d, cnt_q;
    logic [(DATA_WIDTH/64)-1:0][63:0] cache_line_d, cache_line_q;
    // save the address for a read, as we allow for non-cacheline aligned accesses
    logic [(DATA_WIDTH/64)-1:0] addr_offset_d, addr_offset_q;
    logic [AXI_ID_WIDTH-1:0]    id_d, id_q;
    logic [ADDR_INDEX-1:0]      index;

    always_comb begin : axi_fsm
        // Default assignments
        axi.aw_valid  = 1'b0;
        axi.aw_addr   = addr_i;
        axi.aw_prot   = 3'b0;
        axi.aw_region = 4'b0;
        axi.aw_len    = 8'b0;
        axi.aw_size   = {1'b0, size_i};
        axi.aw_burst  = (type_i == SINGLE_REQ) ? 2'b00 :  2'b01;  // fixed size for single request and incremental transfer for everything else
        axi.aw_lock   = 1'b0;
        axi.aw_cache  = 4'b0;
        axi.aw_qos    = 4'b0;
        axi.aw_id     = id_i;
        axi.aw_user   = '0;

        axi.ar_valid  = 1'b0;
        // in case of a single request or wrapping transfer we can simply begin at the address, if we want to request a cache-line
        // with an incremental transfer we need to output the corresponding base address of the cache line
        axi.ar_addr   = (CRITICAL_WORD_FIRST || type_i == SINGLE_REQ) ? addr_i : { addr_i[63:DCACHE_BYTE_OFFSET], {{DCACHE_BYTE_OFFSET}{1'b0}}};
        axi.ar_prot   = 3'b0;
        axi.ar_region = 4'b0;
        axi.ar_len    = 8'b0;
        axi.ar_size   = {1'b0, size_i}; // 8 bytes
        axi.ar_burst  = (type_i == SINGLE_REQ) ? 2'b00 : (CRITICAL_WORD_FIRST ? 2'b10 : 2'b01);  // wrapping transfer in case of a critical word first strategy
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
        gnt_id_o      = '0;
        valid_o       = 1'b0;
        id_o          = axi.r_id;

        // rdata_o   = axi.r_data;
        critical_word_o         = axi.r_data;
        critical_word_valid_o   = 1'b0;
        rdata_o                 = cache_line_q;

        state_d                 = state_q;
        cnt_d                   = cnt_q;
        cache_line_d            = cache_line_q;
        addr_offset_d           = addr_offset_q;
        id_d                    = id_q;
        index                   = '0;

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
                            gnt_id_o = id_i;
                            case ({axi.aw_ready, axi.w_ready})
                                2'b11: state_d = WAIT_B_VALID;
                                2'b01: state_d = WAIT_AW_READY;
                                2'b10: state_d = WAIT_LAST_W_READY;
                                default: state_d = IDLE;
                            endcase
                            id_d = axi.aw_id;
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
                            // save id
                            id_d = axi.aw_id;

                        end
                    // read
                    end else begin

                        axi.ar_valid = 1'b1;
                        gnt_o = axi.ar_ready;
                        gnt_id_o = id_i;

                        if (type_i != SINGLE_REQ) begin
                            axi.ar_len = BURST_SIZE;
                            cnt_d = BURST_SIZE;
                        end

                        if (axi.ar_ready) begin
                            state_d = (type_i == SINGLE_REQ) ? WAIT_R_VALID : WAIT_R_VALID_MULTIPLE;
                            addr_offset_d = addr_i[ADDR_INDEX-1+3:3];
                            // save id
                            id_d = axi.ar_id;
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
                axi.aw_len   = BURST_SIZE;
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
                            gnt_id_o = id_q;
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
                axi.aw_len   = BURST_SIZE;

                if (axi.aw_ready) begin
                    state_d = WAIT_B_VALID;
                    gnt_o = 1'b1;
                    gnt_id_o = id_q;
                end
            end

            // ~> from write, there is an outstanding write
            WAIT_LAST_W_READY: begin
                axi.w_valid = 1'b1;
                axi.w_data  = wdata_i[BURST_SIZE-cnt_q];
                axi.w_strb  = be_i[BURST_SIZE-cnt_q];

                // this is the last write
                axi.w_last  = (cnt_q == '0) ? 1'b1 : 1'b0;

                if (axi.w_ready) begin
                    // last write -> go to WAIT_B_VALID
                    if (cnt_q == '0) begin
                        state_d = WAIT_B_VALID;
                        gnt_o = (cnt_q == '0);
                        gnt_id_o = id_q;
                    end else begin
                        cnt_d = cnt_q - 1;
                    end
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
                if (CRITICAL_WORD_FIRST)
                    index = addr_offset_q + (BURST_SIZE-cnt_q);
                else
                    index = BURST_SIZE-cnt_q;

                // reads are always wrapping here
                axi.r_ready = 1'b1;
                // this is the first read a.k.a the critical word
                if (axi.r_valid) begin
                    if (CRITICAL_WORD_FIRST) begin
                        // this is the first word of a cacheline read, e.g.: the word which was causing the miss
                        if (state_q == WAIT_R_VALID_MULTIPLE && cnt_q == BURST_SIZE) begin
                            critical_word_valid_o = 1'b1;
                            critical_word_o       = axi.r_data;
                        end
                    end else begin
                        // check if the address offset matches - then we are getting the critical word
                        if (index == addr_offset_q) begin
                            critical_word_valid_o = 1'b1;
                            critical_word_o       = axi.r_data;
                        end
                    end

                    // this is the last read
                    if (axi.r_last) begin
                        state_d = COMPLETE_READ;
                    end

                    // save the word
                    if (state_q == WAIT_R_VALID_MULTIPLE) begin
                        cache_line_d[index] = axi.r_data;

                    end else
                        cache_line_d[0] = axi.r_data;

                    // Decrease the counter
                    cnt_d = cnt_q - 1;
                end
            end
            // ~> read is complete
            COMPLETE_READ: begin
                valid_o = 1'b1;
                state_d = IDLE;
                id_o    = id_q;
            end
        endcase
    end

    // ----------------
    // Registers
    // ----------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            // start in flushing state and initialize the memory
            state_q       <= IDLE;
            cnt_q         <= '0;
            cache_line_q  <= '0;
            addr_offset_q <= '0;
            id_q          <= '0;
        end else begin
            state_q       <= state_d;
            cnt_q         <= cnt_d;
            cache_line_q  <= cache_line_d;
            addr_offset_q <= addr_offset_d;
            id_q          <= id_d;
        end
    end

endmodule
