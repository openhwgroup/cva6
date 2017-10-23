/* File:   cache_ctrl.svh
 * Author: Florian Zaruba <zarubaf@ethz.ch>
 * Date:   14.10.2017
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * Description: Cache controller
 */

import ariane_pkg::*;
import nbdcache_pkg::*;

module cache_ctrl #(
        parameter int unsigned SET_ASSOCIATIVITY = 8,
        parameter int unsigned INDEX_WIDTH       = 12,
        parameter int unsigned TAG_WIDTH         = 44,
        parameter int unsigned CACHE_LINE_WIDTH  = 100
    )(
        input  logic                                               clk_i,     // Clock
        input  logic                                               rst_ni,    // Asynchronous reset active low
        input  logic                                               bypass_i,  // enable cache
        output logic                                               busy_o,
        // Core request ports
        input  logic [INDEX_WIDTH-1:0]                             address_index_i,
        input  logic [TAG_WIDTH-1:0]                               address_tag_i,
        input  logic [63:0]                                        data_wdata_i,
        input  logic                                               data_req_i,
        input  logic                                               data_we_i,
        input  logic [7:0]                                         data_be_i,
        input  logic                                               kill_req_i,
        input  logic                                               tag_valid_i,
        output logic                                               data_gnt_o,
        output logic                                               data_rvalid_o,
        output logic [63:0]                                        data_rdata_o,
        input  amo_t                                               amo_op_i,
        // SRAM interface, read only
        output logic [SET_ASSOCIATIVITY-1:0]                       req_o,  // req is valid
        output logic [SET_ASSOCIATIVITY-1:0][INDEX_WIDTH-1:0]      adrr_o, // address into cache array
        input  logic [SET_ASSOCIATIVITY-1:0][CACHE_LINE_WIDTH-1:0] tag_i,
        input  logic [SET_ASSOCIATIVITY-1:0][TAG_WIDTH-1:0]        data_i,
        output logic [SET_ASSOCIATIVITY-1:0]                       we_o,
        // Miss handling
        output miss_req_t                                          miss_req_o,
        // return
        input  logic                                               miss_gnt_i,
        input  logic                                               miss_valid_i,
        input  logic [63:0]                                        miss_data_i,
        input  logic [63:0]                                        critical_word_i,
        input  logic                                               critical_word_valid_i,

        input  logic                                               bypass_gnt_i,
        input  logic                                               bypass_valid_i,
        input  logic [63:0]                                        bypass_data_i,
        // check MSHR for aliasing
        output logic [63:0]                                        mshr_addr_o,
        input  logic                                               mashr_addr_matches_i
);

    enum logic [2:0] {
        IDLE, WAIT_TAG, WAIT_TAG_BYPASSED, WAIT_REFILL_VALID, WAIT_REFILL_GNT
    } state_d, state_q;

    typedef struct packed {
        logic [INDEX_WIDTH-1:0] index;
        logic [TAG_WIDTH-1:0]   tag;
        logic [7:0]             be;
        logic                   we;
        logic [63:0]            wdata;
        logic                   bypass;
    } mem_req_t;

    assign busy_o = (state_q != IDLE);

    mem_req_t mem_req_d, mem_req_q;

    // --------------
    // Cache FSM
    // --------------
    always_comb begin : cache_ctrl_fsm
        // default assignments
        state_d   = state_q;
        mem_req_d = mem_req_q;
        // output assignments
        data_gnt_o    = 1'b0;
        data_rvalid_o = 1'b0;
        data_rdata_o  = '0;

        miss_req_o      = '0;

        case (state_q)

            IDLE: begin

                // a new request arrived
                if (data_req_i) begin
                    // Bypass mode, check for uncacheable address here as well
                    if (bypass_i) begin
                        state_d = WAIT_TAG_BYPASSED;
                        // grant this access
                        data_gnt_o = 1'b1;
                        // save index, be and we
                        mem_req_d.index = address_index_i;
                        mem_req_d.be = data_be_i;
                        mem_req_d.we = data_we_i;
                        mem_req_d.wdata = data_wdata_i;
                        mem_req_d.bypass = 1'b1;
                    // ------------------
                    // Cache is enabled
                    // ------------------
                    end else begin

                    end
                end
            end

            // cache enabled and waiting for tag
            WAIT_TAG: begin

                // HIT CASE

                // MISS CASE

            end

            // its for sure a miss
            WAIT_TAG_BYPASSED: begin
                // the request was killed
                if (kill_req_i)
                    state_d = IDLE;
                else begin
                    // save tag
                    mem_req_d.tag = address_tag_i;
                    state_d = WAIT_REFILL_GNT;
                end
            end

            // ~> wait for grant from miss unit
            WAIT_REFILL_GNT: begin

                miss_req_o.valid = 1'b1;
                miss_req_o.bypass = mem_req_q.bypass;
                miss_req_o.addr = { mem_req_q.tag, mem_req_q.index };
                miss_req_o.be = mem_req_q.be;
                miss_req_o.we = mem_req_q.we;
                miss_req_o.wdata = mem_req_q.wdata;
                // got a grant so go to valid
                if (bypass_gnt_i)
                    state_d = WAIT_REFILL_VALID;

            end

            WAIT_REFILL_VALID: begin
                // got a valid answer
                if (bypass_valid_i) begin
                    data_rdata_o = bypass_data_i;
                    data_rvalid_o = 1'b1;
                    state_d = IDLE;
                end
            end

        endcase
    end

    // --------------
    // Registers
    // --------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            state_q   <= IDLE;
            mem_req_q <= '0;
        end else begin
            state_q   <= state_d;
            mem_req_q <= mem_req_d;
        end
    end
endmodule

module AMO_alu (
        input logic         clk_i,
        input logic         rst_ni,
        // AMO interface
        input  logic        amo_commit_i, // commit atomic memory operation
        output logic        amo_valid_o,  // we have a valid AMO result
        output logic [63:0] amo_result_o, // result of atomic memory operation
        input  logic        amo_flush_i   // forget about AMO
    );

endmodule
