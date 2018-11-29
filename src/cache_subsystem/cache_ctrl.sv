// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File:   cache_ctrl.svh
// Author: Florian Zaruba <zarubaf@ethz.ch>
// Date:   14.10.2017
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// Description: Cache controller

import ariane_pkg::*;
import std_cache_pkg::*;

module cache_ctrl #(
    parameter logic [63:0] CACHE_START_ADDR  = 64'h4000_0000
) (
    input  logic                                 clk_i,     // Clock
    input  logic                                 rst_ni,    // Asynchronous reset active low
    input  logic                                 flush_i,
    input  logic                                 bypass_i,  // enable cache
    output logic                                 busy_o,
    // Core request ports
    input  dcache_req_i_t                        req_port_i,
    output dcache_req_o_t                        req_port_o,
    // SRAM interface
    output logic [DCACHE_SET_ASSOC-1:0]          req_o,  // req is valid
    output logic [DCACHE_INDEX_WIDTH-1:0]        addr_o, // address into cache array
    input  logic                                 gnt_i,
    output cache_line_t                          data_o,
    output cl_be_t                               be_o,
    output logic [DCACHE_TAG_WIDTH-1:0]          tag_o, //valid one cycle later
    input  cache_line_t [DCACHE_SET_ASSOC-1:0]   data_i,
    output logic                                 we_o,
    input  logic [DCACHE_SET_ASSOC-1:0]          hit_way_i,
    // Miss handling
    output miss_req_t                            miss_req_o,
    // return
    input  logic                                 miss_gnt_i,
    input  logic                                 active_serving_i, // the miss unit is currently active for this unit, serving the miss
    input  logic [63:0]                          critical_word_i,
    input  logic                                 critical_word_valid_i,
    // bypass ports
    input  logic                                 bypass_gnt_i,
    input  logic                                 bypass_valid_i,
    input  logic [63:0]                          bypass_data_i,
    // check MSHR for aliasing
    output logic [55:0]                          mshr_addr_o,
    input  logic                                 mshr_addr_matches_i,
    input  logic                                 mshr_index_matches_i
);

    enum logic [3:0] {
        IDLE,               // 0
        WAIT_TAG,           // 1
        WAIT_TAG_BYPASSED,  // 2
        STORE_REQ,          // 3
        WAIT_REFILL_VALID,  // 4
        WAIT_REFILL_GNT,    // 5
        WAIT_TAG_SAVED,     // 6
        WAIT_MSHR,          // 7
        WAIT_CRITICAL_WORD  // 8
    } state_d, state_q;

    typedef struct packed {
        logic [DCACHE_INDEX_WIDTH-1:0] index;
        logic [DCACHE_TAG_WIDTH-1:0]   tag;
        logic [7:0]             be;
        logic [1:0]             size;
        logic                   we;
        logic [63:0]            wdata;
        logic                   bypass;
    } mem_req_t;

    logic [DCACHE_SET_ASSOC-1:0] hit_way_d, hit_way_q;

    assign busy_o = (state_q != IDLE);

    mem_req_t mem_req_d, mem_req_q;

    logic [DCACHE_LINE_WIDTH-1:0] cl_i;

    always_comb begin : way_select
        cl_i = '0;
        for (int unsigned i = 0; i < DCACHE_SET_ASSOC; i++)
            if (hit_way_i[i])
                cl_i = data_i[i].data;

        // cl_i = data_i[one_hot_to_bin(hit_way_i)].data;
    end

    // --------------
    // Cache FSM
    // --------------
    always_comb begin : cache_ctrl_fsm
        automatic logic [$clog2(DCACHE_LINE_WIDTH)-1:0] cl_offset;
        // incoming cache-line -> this is needed as synthesis is not supporting +: indexing in a multi-dimensional array
        // cache-line offset -> multiple of 64
        cl_offset = mem_req_q.index[DCACHE_BYTE_OFFSET-1:3] << 6; // shift by 6 to the left
        // default assignments
        state_d   = state_q;
        mem_req_d = mem_req_q;
        hit_way_d = hit_way_q;
        // output assignments
        req_port_o.data_gnt    = 1'b0;
        req_port_o.data_rvalid = 1'b0;
        req_port_o.data_rdata  = '0;
        miss_req_o    = '0;
        mshr_addr_o   = '0;
        // Memory array communication
        req_o  = '0;
        addr_o = req_port_i.address_index;
        data_o = '0;
        be_o   = '0;
        tag_o  = '0;
        we_o   = '0;
        tag_o  = 'b0;

        case (state_q)

            IDLE: begin
                // a new request arrived
                if (req_port_i.data_req && !flush_i) begin
                    // request the cache line - we can do this speculatively
                    req_o = '1;

                    // save index, be and we
                    mem_req_d.index = req_port_i.address_index;
                    mem_req_d.tag   = req_port_i.address_tag;
                    mem_req_d.be    = req_port_i.data_be;
                    mem_req_d.size  = req_port_i.data_size;
                    mem_req_d.we    = req_port_i.data_we;
                    mem_req_d.wdata = req_port_i.data_wdata;

                    // Bypass mode, check for uncacheable address here as well
                    if (bypass_i) begin
                        state_d = (req_port_i.data_we) ? WAIT_REFILL_GNT : WAIT_TAG_BYPASSED;
                        // grant this access only if it was a load
                        req_port_o.data_gnt = (req_port_i.data_we) ? 1'b0 : 1'b1;
                        mem_req_d.bypass = 1'b1;
                    // ------------------
                    // Cache is enabled
                    // ------------------
                    end else begin
                        // Wait that we have access on the memory array
                        if (gnt_i) begin
                            state_d = WAIT_TAG;
                            mem_req_d.bypass = 1'b0;
                            // only for a read
                            if (!req_port_i.data_we)
                                req_port_o.data_gnt = 1'b1;
                        end
                    end
                end
            end

            // cache enabled and waiting for tag
            WAIT_TAG, WAIT_TAG_SAVED: begin
                // depending on where we come from
                // For the store case the tag comes in the same cycle
                tag_o = (state_q == WAIT_TAG_SAVED || mem_req_q.we) ? mem_req_q.tag
                                                                    : req_port_i.address_tag;
                // we speculatively request another transfer
                if (req_port_i.data_req && !flush_i) begin
                    req_o = '1;
                end

                // check that the client really wants to do the request
                if (!req_port_i.kill_req) begin
                    // ------------
                    // HIT CASE
                    // ------------
                    if (|hit_way_i) begin
                        // we can request another cache-line if this was a load
                        if (req_port_i.data_req && !mem_req_q.we && !flush_i) begin
                            state_d          = WAIT_TAG; // switch back to WAIT_TAG
                            mem_req_d.index  = req_port_i.address_index;
                            mem_req_d.be     = req_port_i.data_be;
                            mem_req_d.size   = req_port_i.data_size;
                            mem_req_d.we     = req_port_i.data_we;
                            mem_req_d.wdata  = req_port_i.data_wdata;
                            mem_req_d.tag    = req_port_i.address_tag;
                            mem_req_d.bypass = 1'b0;

                            req_port_o.data_gnt = gnt_i;

                            if (!gnt_i) begin
                                state_d = IDLE;
                            end
                        end else begin
                            state_d = IDLE;
                        end

                        // this is timing critical
                        // req_port_o.data_rdata = cl_i[cl_offset +: 64];
                        case (mem_req_q.index[3])
                            1'b0: req_port_o.data_rdata = cl_i[63:0];
                            1'b1: req_port_o.data_rdata = cl_i[127:64];
                        endcase

                        // report data for a read
                        if (!mem_req_q.we) begin
                            req_port_o.data_rvalid = 1'b1;
                        // else this was a store so we need an extra step to handle it
                        end else begin
                            state_d = STORE_REQ;
                            hit_way_d = hit_way_i;
                        end
                    // ------------
                    // MISS CASE
                    // ------------
                    end else begin
                        // also save the tag
                        mem_req_d.tag = req_port_i.address_tag;
                        // make a miss request
                        state_d = WAIT_REFILL_GNT;
                    end
                    // ----------------------------------------------
                    // Check MSHR - Miss Status Handling Register
                    // ----------------------------------------------
                    mshr_addr_o = {tag_o, mem_req_q.index};
                    // 1. We've got a match on MSHR and while are going down the
                    //    store path. This means that the miss controller is
                    //    currently evicting our cache-line. As the store is
                    //    non-atomic we need to constantly check whether we are
                    //    matching the address the miss handler is serving.
                    //    Furthermore we need to check for the whole index
                    //    because a completely different memory line could alias
                    //    with the cache-line we are evicting.
                    // 2. The second case is where we are currently loading and
                    //    the address matches the exact CL the miss controller
                    //    is currently serving. That means we need to wait for
                    //    the miss controller to finish its request before we
                    //    can continue to serve this CL. Otherwise we will fetch
                    //    the cache-line again and potentially loosing any
                    //    content we've written so far. This as a consequence
                    //    means we can't have hit on the CL which mean the
                    //    req_port_o.data_rvalid will be de-asserted.
                    if ((mshr_index_matches_i && mem_req_q.we) || mshr_addr_matches_i) begin
                        state_d = WAIT_MSHR;
                        // save tag if we didn't already save it e.g.: we are not in in the Tag saved state
                        if (state_q != WAIT_TAG_SAVED) begin
                            mem_req_d.tag = req_port_i.address_tag;
                        end
                    end

                    // -------------------------
                    // Check for cache-ability
                    // -------------------------
                    if (tag_o < CACHE_START_ADDR[DCACHE_TAG_WIDTH+DCACHE_INDEX_WIDTH-1:DCACHE_INDEX_WIDTH]) begin
                        mem_req_d.tag = req_port_i.address_tag;
                        mem_req_d.bypass = 1'b1;
                        state_d = WAIT_REFILL_GNT;
                    end
                end
            end

            // ~> we are here as we need a second round of memory access for a store
            STORE_REQ: begin
                // check if the MSHR still doesn't match
                mshr_addr_o = {mem_req_q.tag, mem_req_q.index};

                // We need to re-check for MSHR aliasing here as the store requires at least
                // two memory look-ups on a single-ported SRAM and therefore is non-atomic
                if (!mshr_index_matches_i) begin
                    // store data, write dirty bit
                    req_o      = hit_way_q;
                    addr_o     = mem_req_q.index;
                    we_o       = 1'b1;

                    be_o.vldrty = hit_way_q;

                    // set the correct byte enable
                    be_o.data[cl_offset>>3 +: 8]  = mem_req_q.be;
                    data_o.data[cl_offset  +: 64] = mem_req_q.wdata;
                    // ~> change the state
                    data_o.dirty = 1'b1;
                    data_o.valid = 1'b1;

                    // got a grant ~> this is finished now
                    if (gnt_i) begin
                        req_port_o.data_gnt = 1'b1;
                        state_d = IDLE;
                    end
                end else begin
                    state_d = WAIT_MSHR;
                end
            end // case: STORE_REQ

            // we've got a match on MSHR ~> miss unit is currently serving a request
            WAIT_MSHR: begin
                mshr_addr_o = {mem_req_q.tag, mem_req_q.index};
                // we can start a new request
                if (!mshr_index_matches_i) begin
                    req_o = '1;

                    addr_o = mem_req_q.index;

                    if (gnt_i) state_d = WAIT_TAG_SAVED;
                end
            end

            // its for sure a miss
            WAIT_TAG_BYPASSED: begin
                // the request was killed
                if (!req_port_i.kill_req) begin
                    // save tag
                    mem_req_d.tag = req_port_i.address_tag;
                    state_d = WAIT_REFILL_GNT;
                end
            end

            // ~> wait for grant from miss unit
            WAIT_REFILL_GNT: begin

                mshr_addr_o = {mem_req_q.tag, mem_req_q.index};

                miss_req_o.valid = 1'b1;
                miss_req_o.bypass = mem_req_q.bypass;
                miss_req_o.addr = {mem_req_q.tag, mem_req_q.index};
                miss_req_o.be = mem_req_q.be;
                miss_req_o.size = mem_req_q.size;
                miss_req_o.we = mem_req_q.we;
                miss_req_o.wdata = mem_req_q.wdata;

                // got a grant so go to valid
                if (bypass_gnt_i) begin
                    state_d = WAIT_REFILL_VALID;
                    // if this was a write we still need to give a grant to the store unit
                    if (mem_req_q.we)
                        req_port_o.data_gnt = 1'b1;
                end

                if (miss_gnt_i && !mem_req_q.we)
                    state_d = WAIT_CRITICAL_WORD;
                else if (miss_gnt_i) begin
                    state_d = IDLE;
                    req_port_o.data_gnt = 1'b1;
                end

                // it can be the case that the miss unit is currently serving a
                // request which matches ours
                // so we need to check the MSHR for matching continuously
                // if the MSHR matches we need to go to a different state -> we should never get a matching MSHR and a high miss_gnt_i
                if (mshr_addr_matches_i && !active_serving_i) begin
                    state_d = WAIT_MSHR;
                end
            end

            // ~> wait for critical word to arrive
            WAIT_CRITICAL_WORD: begin
                // speculatively request another word
                if (req_port_i.data_req) begin
                    // request the cache line
                    req_o = '1;
                end

                if (critical_word_valid_i) begin
                    req_port_o.data_rvalid = 1'b1;
                    req_port_o.data_rdata = critical_word_i;
                    // we can make another request
                    if (req_port_i.data_req) begin
                        // save index, be and we
                        mem_req_d.index = req_port_i.address_index;
                        mem_req_d.be    = req_port_i.data_be;
                        mem_req_d.size  = req_port_i.data_size;
                        mem_req_d.we    = req_port_i.data_we;
                        mem_req_d.wdata = req_port_i.data_wdata;
                        mem_req_d.tag   = req_port_i.address_tag;

                        state_d = IDLE;

                        // Wait until we have access on the memory array
                        if (gnt_i) begin
                            state_d = WAIT_TAG;
                            mem_req_d.bypass = 1'b0;
                            req_port_o.data_gnt = 1'b1;
                        end
                    end else begin
                        state_d = IDLE;
                    end
                end
            end
            // ~> wait until the bypass request is valid
            WAIT_REFILL_VALID: begin
                // got a valid answer
                if (bypass_valid_i) begin
                    req_port_o.data_rdata = bypass_data_i;
                    req_port_o.data_rvalid = 1'b1;
                    state_d = IDLE;
                end
            end
        endcase

        if (req_port_i.kill_req) begin
            state_d = IDLE;
            req_port_o.data_rvalid = 1'b1;
        end
    end

    // --------------
    // Registers
    // --------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q       <= IDLE;
            mem_req_q     <= '0;
            hit_way_q     <= '0;
        end else begin
            state_q   <= state_d;
            mem_req_q <= mem_req_d;
            hit_way_q <= hit_way_d;
        end
    end

    //pragma translate_off
    `ifndef VERILATOR
        initial begin
            assert (DCACHE_LINE_WIDTH == 128) else $error ("Cacheline width has to be 128 for the moment. But only small changes required in data select logic");
        end
        // if the full MSHR address matches so should also match the partial one
        partial_full_mshr_match: assert property(@(posedge  clk_i) disable iff (~rst_ni) mshr_addr_matches_i -> mshr_index_matches_i)   else $fatal (1, "partial mshr index doesn't match");
        // there should never be a valid answer when the MSHR matches and we are not being served
        no_valid_on_mshr_match: assert property(@(posedge  clk_i) disable iff (~rst_ni) (mshr_addr_matches_i && !active_serving_i)-> !req_port_o.data_rvalid || req_port_i.kill_req) else $fatal (1, "rvalid_o should not be set on MSHR match");
    `endif
    //pragma translate_on
endmodule
