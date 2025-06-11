/*
 *  Copyright 2023 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/*
 *  Authors       : Riccardo Alidori, Cesar Fuguet
 *  Maintainers(s): Cesar Fuguet
 *  Creation Date : June, 2021
 *  Description   : HPDcache Linear Hardware Memory Prefetcher.
 *  History       :
 */
module hwpf_stride
import hwpf_stride_pkg::*;
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,
    parameter type hpdcache_nline_t = logic,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_set_t = logic,
    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input  logic                        clk_i,
    input  logic                        rst_ni,

    // CSR
    input  logic                        csr_base_set_i,
    input  hwpf_stride_base_t           csr_base_i,
    input  logic                        csr_param_set_i,
    input  hwpf_stride_param_t          csr_param_i,
    input  logic                        csr_throttle_set_i,
    input  hwpf_stride_throttle_t       csr_throttle_i,

    output hwpf_stride_base_t           csr_base_o,
    output hwpf_stride_param_t          csr_param_o,
    output hwpf_stride_throttle_t       csr_throttle_o,

    // If high, the prefetcher is enabled and active
    output logic                        busy_o,

    // Snooping
    //   Address to snoop on requests ports
    output hpdcache_nline_t             snoop_nline_o,
    //   If set to one, the snoop address matched one of the requests
    input  logic                        snoop_match_i,

    // D-Cache interface
    output logic                        hpdcache_req_valid_o,
    input  logic                        hpdcache_req_ready_i,
    output hpdcache_req_t               hpdcache_req_o,
    input  logic                        hpdcache_rsp_valid_i,
    input  hpdcache_rsp_t               hpdcache_rsp_i
);
//  }}}

    //  Definition of constants
    //  {{{
    localparam int STRIDE_WIDTH     = $bits(csr_param_i.stride);
    localparam int NBLOCKS_WIDTH    = $bits(csr_param_i.nblocks);
    localparam int NLINES_WIDTH     = $bits(csr_param_i.nlines);
    localparam int NWAIT_WIDTH      = $bits(csr_throttle_i.nwait);
    localparam int INFLIGHT_WIDTH   = $bits(csr_throttle_i.ninflight);
    localparam int NLINES_CNT_WIDTH = NLINES_WIDTH;
    //  }}}

    //  Internal registers and signals
    //  {{{
    //      FSM
    typedef enum {
        IDLE,
        SNOOP,
        SEND_REQ,
        WAIT,
        DONE,
        ABORT
    } hwpf_stride_fsm_t;

    hwpf_stride_fsm_t state_d, state_q;

    logic [NBLOCKS_WIDTH-1:0] nblocks_cnt_d, nblocks_cnt_q;
    logic [NLINES_CNT_WIDTH-1:0] nlines_cnt_d, nlines_cnt_q;
    logic [NWAIT_WIDTH-1:0] nwait_cnt_d, nwait_cnt_q;
    logic [INFLIGHT_WIDTH-1:0] inflight_cnt_d, inflight_cnt_q;
    logic inflight_inc, inflight_dec;

    hwpf_stride_base_t csr_base_q;
    hwpf_stride_base_t shadow_base_q, shadow_base_d;
    hwpf_stride_param_t csr_param_q;
    hwpf_stride_param_t shadow_param_q, shadow_param_d;
    hwpf_stride_throttle_t csr_throttle_q;
    hwpf_stride_throttle_t shadow_throttle_q, shadow_throttle_d;
    hpdcache_nline_t request_nline_q, request_nline_d;

    hpdcache_set_t hpdcache_req_set;
    hpdcache_tag_t hpdcache_req_tag;

    logic csr_base_update;
    hpdcache_nline_t increment_stride;
    logic is_inflight_max;

    //      Default assignment
    assign increment_stride = hpdcache_nline_t'(shadow_param_q.stride) + 1'b1;
    assign inflight_dec     = hpdcache_rsp_valid_i;
    assign snoop_nline_o    = shadow_base_q.base_cline;
    assign is_inflight_max  = (shadow_throttle_q.ninflight == '0) ?
                              1'b0 : (inflight_cnt_q >= shadow_throttle_q.ninflight);
    assign csr_base_o       = csr_base_q;
    assign csr_param_o      = csr_param_q;
    assign csr_throttle_o   = csr_throttle_q;
    //  }}}

    //  Dcache outputs
    //  {{{
    assign hpdcache_req_set = request_nline_q[0 +: HPDcacheCfg.setWidth],
           hpdcache_req_tag = request_nline_q[HPDcacheCfg.setWidth +: HPDcacheCfg.tagWidth];

    assign hpdcache_req_o.addr_offset     = { hpdcache_req_set, {HPDcacheCfg.clOffsetWidth{1'b0}} },
           hpdcache_req_o.wdata           = '0,
           hpdcache_req_o.op              = HPDCACHE_REQ_CMO_PREFETCH,
           hpdcache_req_o.be              = '1,
           hpdcache_req_o.size            = '0,
           hpdcache_req_o.sid             = '0, // this is set when connecting to the dcache
           hpdcache_req_o.tid             = '0, // this is set by the wrapper of the prefetcher
           hpdcache_req_o.need_rsp        = 1'b1,
           hpdcache_req_o.phys_indexed    = 1'b1,
           hpdcache_req_o.addr_tag        = hpdcache_req_tag,
           hpdcache_req_o.pma.uncacheable = 1'b0,
           hpdcache_req_o.pma.io          = 1'b0;
    //  }}}

    //  Set state of internal registers
    //  {{{
    always_ff @(posedge clk_i or negedge rst_ni)
    begin
        if (!rst_ni) begin
            csr_base_q <= '0;
            csr_param_q <= '0;
            shadow_base_q <= '0;
            shadow_param_q <= '0;
            shadow_throttle_q <= '0;
            request_nline_q <= '0;
            state_q <= IDLE;
        end else begin
            if      (csr_base_set_i) csr_base_q <= csr_base_i;
            else if (csr_base_update) csr_base_q <= shadow_base_d;
            if      (csr_param_set_i) csr_param_q <= csr_param_i;
            if      (csr_throttle_set_i) csr_throttle_q <= csr_throttle_i;
            shadow_base_q <= shadow_base_d;
            shadow_param_q <= shadow_param_d;
            shadow_throttle_q <= shadow_throttle_d;
            request_nline_q <= request_nline_d;
            state_q <= state_d;
        end
    end
    //  }}}

    //  Update internal counters
    //  {{{
    always_comb begin : inflight_cnt
        inflight_cnt_d = inflight_cnt_q;

        // Every time we send a dcache request, increment the counter
        if ( inflight_inc ) begin
            inflight_cnt_d++;
        end

        // Every time we got a response from the cache, decrement the counter
        if ( inflight_dec && ( inflight_cnt_q > 0 )) begin
            inflight_cnt_d--;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            nblocks_cnt_q  <= '0;
            nlines_cnt_q <= '0;
            nwait_cnt_q <= '0;
            inflight_cnt_q <= '0;
        end else begin
            nblocks_cnt_q <= nblocks_cnt_d;
            nlines_cnt_q <= nlines_cnt_d;
            nwait_cnt_q <= nwait_cnt_d;
            inflight_cnt_q <= inflight_cnt_d;
        end
    end
    //  }}}

    //  FSM
    //  {{{
    always_comb begin : fsm_control
        // default assignments
        hpdcache_req_valid_o = 1'b0;
        nblocks_cnt_d = nblocks_cnt_q;
        nlines_cnt_d = nlines_cnt_q;
        nwait_cnt_d = nwait_cnt_q;
        inflight_inc = 1'b0;
        busy_o = 1'b0;
        csr_base_update = 1'b0;

        shadow_base_d = shadow_base_q;
        shadow_param_d = shadow_param_q;
        shadow_throttle_d = shadow_throttle_q;
        request_nline_d = request_nline_q;
        state_d = state_q;

        unique case ( state_q )

            IDLE: begin
                // If enabled, go snooping the dcache ports
                if ( csr_base_q.enable ) begin
                    shadow_base_d = csr_base_q;
                    if (( csr_param_q.nlines > 0 ) || ( csr_param_q.nblocks > 0 )) begin
                        shadow_param_d = csr_param_q;
                        shadow_throttle_d = csr_throttle_q;
                        state_d = SNOOP;
                    end else begin
                        // no prefetch needed, disarm immediately
                        shadow_base_d.enable = 1'b0;
                        csr_base_update = 1'b1;
                    end
                end
            end


            SNOOP: begin
                if ( csr_base_q.enable ) begin
                    // If a snooper matched an address, send the request
                    if ( snoop_match_i ) begin
                        state_d = SEND_REQ;

                        if ( shadow_param_q.nlines == 0 ) begin
                            //  skip the first block
                            request_nline_d = shadow_base_q.base_cline +
                                              hpdcache_nline_t'(increment_stride);
                            nblocks_cnt_d = ( shadow_param_q.nblocks > 0 ) ?
                                            shadow_param_q.nblocks - 1 : 0;
                            nlines_cnt_d = 0;

                            //  update the base cacheline to the first one of the next block
                            shadow_base_d.base_cline = request_nline_d;
                        end else begin
                            //  skip the first cacheline (of the first block)
                            request_nline_d = shadow_base_q.base_cline + 1'b1;
                            nblocks_cnt_d = shadow_param_q.nblocks;
                            nlines_cnt_d = shadow_param_q.nlines - 1;
                        end
                    end
                end else begin
                    state_d = IDLE;
                end
            end


            SEND_REQ: begin
                busy_o = 1'b1;

                // make the prefetch request to memory
                hpdcache_req_valid_o = 1'b1;

                // we've got a grant, so we can move to the next request
                if ( hpdcache_req_ready_i ) begin
                    inflight_inc = 1'b1;

                    if ( nlines_cnt_q == 0 ) begin
                        //  go to the first cacheline of the next block
                        request_nline_d = shadow_base_q.base_cline +
                                          hpdcache_nline_t'(increment_stride);
                        nblocks_cnt_d = ( nblocks_cnt_q > 0 ) ? nblocks_cnt_q - 1 : 0;
                        nlines_cnt_d = shadow_param_q.nlines;

                        //  update the base cacheline to the first one of the next block
                        shadow_base_d.base_cline = request_nline_d;
                    end else begin
                        //  go to the next cacheline (within the same block)
                        request_nline_d = request_nline_q + 1'b1;
                        nlines_cnt_d = nlines_cnt_q - 1;
                    end

                    // if the NWAIT parameter is equal 0, we can issue a request every cycle
                    if (( nblocks_cnt_q == 0 ) && ( nlines_cnt_q == 0 )) begin
                        state_d = DONE;
                    end else if ( shadow_throttle_q.nwait == 0 ) begin
                        // Wait if the number of inflight requests is greater than
                        // the maximum indicated. Otherwise, send the next request
                        state_d = is_inflight_max ? WAIT : SEND_REQ;
                    end else begin
                        // Wait the indicated cycles before sending the next request
                        nwait_cnt_d = shadow_throttle_q.nwait;
                        state_d = WAIT;
                    end

                    if ( !csr_base_q.enable ) state_d = ABORT;
                end
            end


            WAIT: begin
                //  Wait until:
                //    - the indicated number of wait cycles between requests is reached (nwait)
                //    - the number of inflight requests is below the indicated maximum (ninflight)
                busy_o = 1'b1;
                if ( csr_base_q.enable ) begin
                    if ( !is_inflight_max && ( nwait_cnt_q == 0 )) begin
                        state_d = SEND_REQ;
                    end

                    if ( nwait_cnt_q > 0 ) begin
                        nwait_cnt_d = nwait_cnt_q - 1;
                    end
                end else begin
                    state_d = ABORT;
                end
            end


            DONE: begin
                busy_o = 1'b1;
                if ( csr_base_q.enable ) begin
                    if (( inflight_cnt_q == 0 ) && !is_inflight_max && ( nwait_cnt_q == 0 )) begin
                        // Copy back shadow base register into the user visible one
                        csr_base_update = 1'b1;

                        // Check the rearm bit
                        if ( shadow_base_q.rearm ) begin
                            state_d = SNOOP;
                        end else begin
                            state_d = IDLE;

                            // disarm the prefetcher
                            shadow_base_d.enable = 1'b0;
                        end

                        // Check the cycle bit
                        if ( shadow_base_q.cycle ) begin
                            // restore the base address
                            shadow_base_d.base_cline = csr_base_q.base_cline;
                        end
                    end

                    if ( nwait_cnt_q > 0 ) begin
                        nwait_cnt_d = nwait_cnt_q - 1;
                    end
                end else begin
                    state_d = ABORT;
                end
            end

            ABORT: begin
                busy_o = 1'b1;
                if ( inflight_cnt_q == 0 ) begin
                    state_d = IDLE;
                end
            end
        endcase
    end
    //  }}}
endmodule
