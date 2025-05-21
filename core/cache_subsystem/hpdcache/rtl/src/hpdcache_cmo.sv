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
 *  Authors       : Cesar Fuguet
 *  Creation Date : July, 2021
 *  Description   : HPDcache Cache-Management-Operation Handler
 *  History       :
 */
module hpdcache_cmo
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    parameter type hpdcache_nline_t = logic,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_set_t = logic,
    parameter type hpdcache_data_word_t = logic,
    parameter type hpdcache_way_vector_t = logic,

    parameter type hpdcache_rsp_t = logic,
    parameter type hpdcache_req_addr_t = logic,
    parameter type hpdcache_req_tid_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_data_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,

    //  Global control signals
    //  {{{
    input  logic                  wbuf_empty_i,
    input  logic                  mshr_empty_i,
    input  logic                  rtab_empty_i,
    input  logic                  ctrl_empty_i,
    //  }}}

    //  Request interface
    //  {{{
    input  logic                  req_valid_i,
    output logic                  req_ready_o,
    input  hpdcache_cmoh_op_t     req_op_i,
    input  hpdcache_req_addr_t    req_addr_i,
    input  hpdcache_req_data_t    req_wdata_i/*unused*/,
    input  hpdcache_req_sid_t     req_sid_i,
    input  hpdcache_req_tid_t     req_tid_i,
    input  logic                  req_need_rsp_i,
    output logic                  req_wait_o,
    //  }}}

    //  Core response interface
    //  {{{
    input  logic                  core_rsp_ready_i,
    output logic                  core_rsp_valid_o,
    output hpdcache_rsp_t         core_rsp_o,
    //  }}}

    //  Write Buffer Interface
    //  {{{
    output logic                  wbuf_flush_all_o,
    //  }}}

    //  Cache Directory Interface
    //  {{{
    output logic                  dir_check_nline_o,
    output hpdcache_set_t         dir_check_nline_set_o,
    output hpdcache_tag_t         dir_check_nline_tag_o,
    input  hpdcache_way_vector_t  dir_check_nline_hit_way_i,
    input  logic                  dir_check_nline_wback_i,
    input  logic                  dir_check_nline_dirty_i,

    output logic                  dir_check_entry_o,
    output hpdcache_set_t         dir_check_entry_set_o,
    output hpdcache_way_vector_t  dir_check_entry_way_o,
    input  logic                  dir_check_entry_valid_i,
    input  logic                  dir_check_entry_wback_i,
    input  logic                  dir_check_entry_dirty_i,
    input  hpdcache_tag_t         dir_check_entry_tag_i,

    output logic                  dir_updt_o,
    output hpdcache_set_t         dir_updt_set_o,
    output hpdcache_way_vector_t  dir_updt_way_o,
    output logic                  dir_updt_valid_o,
    output logic                  dir_updt_wback_o,
    output logic                  dir_updt_dirty_o,
    output logic                  dir_updt_fetch_o,
    output hpdcache_tag_t         dir_updt_tag_o,
    // }}}

    //  Flush Controller Interface
    //  {{{
    input  logic                  flush_empty_i,
    output logic                  flush_alloc_o,
    input  logic                  flush_alloc_ready_i,
    output hpdcache_nline_t       flush_alloc_nline_o,
    output hpdcache_way_vector_t  flush_alloc_way_o
    // }}}
);
//  }}}

//  Definition of constants and types
//  {{{
    typedef enum {
        CMOH_IDLE,
        CMOH_FENCE_WAIT_WBUF_RTAB_EMPTY,
        CMOH_WAIT_MSHR_RTAB_EMPTY,
        CMOH_INVAL_CHECK_NLINE,
        CMOH_INVAL_SET,
        CMOH_FLUSH_ALL_FIRST,
        CMOH_FLUSH_ALL_NEXT,
        CMOH_FLUSH_ALL_LAST,
        CMOH_FLUSH_NLINE_FIRST,
        CMOH_FLUSH_NLINE_NEXT
    } hpdcache_cmoh_fsm_t;
//  }}}

//  Internal signals and registers
//  {{{
    hpdcache_cmoh_fsm_t   cmoh_fsm_q, cmoh_fsm_d;
    hpdcache_cmoh_op_t    cmoh_op_q, cmoh_op_d;
    hpdcache_req_addr_t   cmoh_addr_q, cmoh_addr_d;
    hpdcache_way_vector_t cmoh_way_q, cmoh_way_d;
    hpdcache_set_t        cmoh_set_q, cmoh_set_d;

    logic                 cmoh_flush_req_valid_q, cmoh_flush_req_valid_d;
    hpdcache_set_t        cmoh_flush_req_set_q, cmoh_flush_req_set_d;
    hpdcache_way_vector_t cmoh_flush_req_way_q, cmoh_flush_req_way_d;
    logic                 cmoh_flush_req_inval_q, cmoh_flush_req_inval_d;

    logic                 cmoh_dir_check_nline_hit;
    hpdcache_nline_t      cmoh_nline;
    hpdcache_set_t        cmoh_set;
    hpdcache_tag_t        cmoh_tag;
    logic                 cmoh_flush_req_w;
    logic                 cmoh_flush_req_wok;
    hpdcache_set_t        cmoh_flush_req_set;
    hpdcache_tag_t        cmoh_flush_req_tag;
    hpdcache_way_vector_t cmoh_flush_req_way;

    logic                 core_rsp_w, core_rsp_r, core_rsp_rok;
    hpdcache_rsp_t        core_rsp;
    logic                 core_rsp_send_q, core_rsp_send_d;

    logic cmoh_set_incr, cmoh_set_reset, cmoh_set_last;
    logic cmoh_way_incr, cmoh_way_reset, cmoh_way_last;
//  }}}

//  CMO core response buffer
//  {{{
    hpdcache_sync_buffer #(
        .FEEDTHROUGH (1'b0),
        .data_t      (hpdcache_rsp_t)
    ) cmoh_core_rsp_buffer_i(
        .clk_i,
        .rst_ni,
        .w_i         (core_rsp_w),
        .wok_o       (/*unused*/),
        .wdata_i     (core_rsp),
        .r_i         (core_rsp_r),
        .rok_o       (core_rsp_rok),
        .rdata_o     (core_rsp_o)
    );

    assign core_rsp_r       = core_rsp_send_q & core_rsp_ready_i;
    assign core_rsp_valid_o = core_rsp_rok    & core_rsp_send_q;
//  }}}

//  CMO request handler FSM
//  {{{
    assign cmoh_nline = cmoh_addr_q[HPDcacheCfg.clOffsetWidth +: HPDcacheCfg.nlineWidth];
    assign cmoh_set   =  cmoh_nline[0                         +: HPDcacheCfg.setWidth];
    assign cmoh_tag   =  cmoh_nline[HPDcacheCfg.setWidth      +: HPDcacheCfg.tagWidth];

    assign req_wait_o  = (cmoh_fsm_q == CMOH_FENCE_WAIT_WBUF_RTAB_EMPTY) |
                         (cmoh_fsm_q == CMOH_WAIT_MSHR_RTAB_EMPTY);

    assign cmoh_dir_check_nline_hit = |dir_check_nline_hit_way_i;

    assign core_rsp = '{
        rdata: '0,
        sid: req_sid_i,
        tid: req_tid_i,
        error: 1'b0,
        aborted: 1'b0
    };

    always_comb
    begin : cmoh_fsm_comb
        cmoh_fsm_d = cmoh_fsm_q;

        cmoh_op_d   = cmoh_op_q;
        cmoh_addr_d = cmoh_addr_q;

        cmoh_flush_req_valid_d = cmoh_flush_req_valid_q;
        cmoh_flush_req_set_d   = cmoh_flush_req_set_q;
        cmoh_flush_req_way_d   = cmoh_flush_req_way_q;
        cmoh_flush_req_inval_d = cmoh_flush_req_inval_q;

        cmoh_set_incr  = 1'b0;
        cmoh_set_reset = 1'b0;
        cmoh_way_incr  = 1'b0;
        cmoh_way_reset = 1'b0;

        dir_check_nline_o     = 1'b0;
        dir_check_nline_set_o = cmoh_set;
        dir_check_nline_tag_o = cmoh_tag;
        dir_check_entry_o     = 1'b0;
        dir_check_entry_set_o = cmoh_set_q;
        dir_check_entry_way_o = cmoh_way_q;

        dir_updt_o       = 1'b0;
        dir_updt_set_o   = '0;
        dir_updt_way_o   = '0;
        dir_updt_valid_o = 1'b0;
        dir_updt_wback_o = 1'b0;
        dir_updt_dirty_o = 1'b0;
        dir_updt_fetch_o = 1'b0;
        dir_updt_tag_o   = '0;

        wbuf_flush_all_o = 1'b0;

        cmoh_flush_req_set = '0;
        cmoh_flush_req_way = '0;
        cmoh_flush_req_tag = '0;

        core_rsp_w      = 1'b0;
        core_rsp_send_d = core_rsp_send_q;

        req_ready_o = 1'b0;

        cmoh_fsm_d = cmoh_fsm_q;

        unique case (cmoh_fsm_q)
            CMOH_IDLE: begin
                req_ready_o = ~core_rsp_rok | core_rsp_r;

                if (core_rsp_r) begin
                    core_rsp_send_d = 1'b0;
                end

                if (req_valid_i && req_ready_o) begin
                    core_rsp_w = req_need_rsp_i;

                    unique case (1'b1)
                        req_op_i.is_fence: begin
                            //  request to the write buffer to send all open entries
                            wbuf_flush_all_o = rtab_empty_i;

                            //  then wait for the write buffer to be empty
                            if (!rtab_empty_i || !wbuf_empty_i) begin
                                cmoh_fsm_d = CMOH_FENCE_WAIT_WBUF_RTAB_EMPTY;
                            end else begin
                                core_rsp_send_d = req_need_rsp_i;
                            end
                        end

                        req_op_i.is_inval_by_nline,
                        req_op_i.is_inval_all,
                        req_op_i.is_flush_by_nline,
                        req_op_i.is_flush_all,
                        req_op_i.is_flush_inval_by_nline,
                        req_op_i.is_flush_inval_all: begin
                            cmoh_op_d      = req_op_i;
                            cmoh_addr_d    = req_addr_i;
                            cmoh_way_reset = 1'b1;
                            cmoh_set_reset = 1'b1;
                            if (mshr_empty_i && rtab_empty_i && ctrl_empty_i) begin // CMO
                                unique if (req_op_i.is_inval_by_nline) begin
                                    cmoh_fsm_d = CMOH_INVAL_CHECK_NLINE;
                                end else if (req_op_i.is_inval_all) begin
                                    cmoh_fsm_d = CMOH_INVAL_SET;
                                end else if (req_op_i.is_flush_by_nline) begin
                                    cmoh_flush_req_inval_d = 1'b0;
                                    cmoh_fsm_d = CMOH_FLUSH_NLINE_FIRST;
                                end else if (req_op_i.is_flush_all) begin
                                    cmoh_flush_req_inval_d = 1'b0;
                                    cmoh_fsm_d = CMOH_FLUSH_ALL_FIRST;
                                end else if (req_op_i.is_flush_inval_by_nline) begin
                                    cmoh_flush_req_inval_d = 1'b1;
                                    cmoh_fsm_d = CMOH_FLUSH_NLINE_FIRST;
                                end else if (req_op_i.is_flush_inval_all) begin
                                    cmoh_flush_req_inval_d = 1'b1;
                                    cmoh_fsm_d = CMOH_FLUSH_ALL_FIRST;
                                end
                            end else begin
                                cmoh_fsm_d = CMOH_WAIT_MSHR_RTAB_EMPTY;
                            end
                        end
                    endcase
                end
            end
            CMOH_FENCE_WAIT_WBUF_RTAB_EMPTY: begin
                wbuf_flush_all_o = rtab_empty_i;
                if (wbuf_empty_i && rtab_empty_i) begin
                    core_rsp_send_d = core_rsp_rok;
                    cmoh_fsm_d = CMOH_IDLE;
                end
            end
            CMOH_WAIT_MSHR_RTAB_EMPTY: begin
                if (mshr_empty_i && rtab_empty_i && ctrl_empty_i) begin
                    unique if (cmoh_op_q.is_inval_by_nline) begin
                        cmoh_fsm_d = CMOH_INVAL_CHECK_NLINE;
                    end else if (cmoh_op_q.is_inval_all) begin
                        cmoh_fsm_d = CMOH_INVAL_SET;
                    end else if (cmoh_op_q.is_flush_by_nline) begin
                        cmoh_flush_req_inval_d = 1'b0;
                        cmoh_fsm_d = CMOH_FLUSH_NLINE_FIRST;
                    end else if (cmoh_op_q.is_flush_all) begin
                        cmoh_flush_req_inval_d = 1'b0;
                        cmoh_fsm_d = CMOH_FLUSH_ALL_FIRST;
                    end else if (cmoh_op_q.is_flush_inval_by_nline) begin
                        cmoh_flush_req_inval_d = 1'b1;
                        cmoh_fsm_d = CMOH_FLUSH_NLINE_FIRST;
                    end else if (cmoh_op_q.is_flush_inval_all) begin
                        cmoh_flush_req_inval_d = 1'b1;
                        cmoh_fsm_d = CMOH_FLUSH_ALL_FIRST;
                    end
                end
            end
            CMOH_INVAL_CHECK_NLINE: begin
                dir_check_nline_o = 1'b1;
                cmoh_fsm_d = CMOH_INVAL_SET;
            end
            CMOH_INVAL_SET: begin
                unique case (1'b1)
                    //  The CMO requests the invalidation of a given cacheline (or flush with
                    //  invalidation when the cache does not support WB policy)
                    cmoh_op_q.is_inval_by_nline,
                    cmoh_op_q.is_flush_inval_by_nline: begin
                        /* FIXME this adds a DIR to DIR timing path. We should probably delay the
                         *       invalidation of one cycle to ease the timing closure */
                        dir_updt_o       = cmoh_dir_check_nline_hit;
                        dir_updt_set_o   = cmoh_set;
                        dir_updt_way_o   = dir_check_nline_hit_way_i;
                        dir_updt_valid_o = 1'b0;
                        dir_updt_wback_o = 1'b0;
                        dir_updt_dirty_o = 1'b0;
                        dir_updt_fetch_o = 1'b0;
                        dir_updt_tag_o   = '0;

                        core_rsp_send_d = core_rsp_rok;
                        cmoh_fsm_d      = CMOH_IDLE;
                    end

                    //  The CMO requests a full invalidation (or flush with invalidation when the
                    //  cache does not support WB policy)
                    cmoh_op_q.is_inval_all,
                    cmoh_op_q.is_flush_inval_all:
                    begin
                        dir_updt_o       = 1'b1;
                        dir_updt_set_o   = cmoh_set_q;
                        dir_updt_way_o   = {HPDcacheCfg.u.ways{1'b1}};
                        dir_updt_valid_o = 1'b0;
                        dir_updt_wback_o = 1'b0;
                        dir_updt_dirty_o = 1'b0;
                        dir_updt_fetch_o = 1'b0;
                        dir_updt_tag_o   = '0;
                        cmoh_set_incr   = 1'b1;
                        if (cmoh_set_last) begin
                            core_rsp_send_d = core_rsp_rok;
                            cmoh_fsm_d = CMOH_IDLE;
                        end
                    end
                endcase
            end
            CMOH_FLUSH_ALL_FIRST: begin
                if (HPDcacheCfg.u.wbEn) begin
                    if (cmoh_flush_req_wok) begin
                        dir_check_entry_o = 1'b1;
                        cmoh_set_incr = cmoh_way_last;
                        cmoh_way_incr = 1'b1;
                        cmoh_flush_req_valid_d = 1'b1;
                        cmoh_flush_req_set_d = cmoh_set_q;
                        cmoh_flush_req_way_d = cmoh_way_q;
                        cmoh_fsm_d = CMOH_FLUSH_ALL_NEXT;
                    end
                end else if (cmoh_flush_req_inval_q) begin
                    cmoh_fsm_d = CMOH_INVAL_SET;
                end else begin
                    core_rsp_send_d = core_rsp_rok;
                    cmoh_fsm_d = CMOH_IDLE;
                end
            end
            CMOH_FLUSH_ALL_NEXT: begin
                if (cmoh_flush_req_valid_q) begin
                    dir_updt_o = dir_check_entry_valid_i &
                        (dir_check_entry_dirty_i | cmoh_flush_req_inval_q);

                    dir_updt_set_o   = cmoh_flush_req_set_q;
                    dir_updt_way_o   = cmoh_flush_req_way_q;
                    dir_updt_valid_o = ~cmoh_flush_req_inval_q;
                    dir_updt_wback_o = ~cmoh_flush_req_inval_q & dir_check_entry_wback_i;
                    dir_updt_dirty_o = 1'b0;
                    dir_updt_fetch_o = 1'b0;
                    dir_updt_tag_o   = dir_check_entry_tag_i;

                    cmoh_flush_req_set = cmoh_flush_req_set_q;
                    cmoh_flush_req_way = cmoh_flush_req_way_q;
                    cmoh_flush_req_tag = dir_check_entry_tag_i;

                    //  The CMO handler needs to dedicate one cycle to
                    //  check the directory and one cycle to update that entry.
                    //  This means that the CMO handler takes 2 cycles per flush request
                    cmoh_flush_req_valid_d = 1'b0;
                end

                if (!cmoh_flush_req_valid_q && cmoh_flush_req_wok) begin
                    dir_check_entry_o = 1'b1;
                    cmoh_set_incr = cmoh_way_last;
                    cmoh_way_incr = 1'b1;
                    cmoh_flush_req_valid_d = 1'b1;
                    cmoh_flush_req_set_d = cmoh_set_q;
                    cmoh_flush_req_way_d = cmoh_way_q;

                    if (cmoh_set_last && cmoh_way_last) begin
                        cmoh_fsm_d = CMOH_FLUSH_ALL_LAST;
                    end
                end
            end
            CMOH_FLUSH_ALL_LAST: begin
                cmoh_flush_req_valid_d = 1'b0;
                if (cmoh_flush_req_valid_q) begin
                    dir_updt_o = dir_check_entry_valid_i &
                        (dir_check_entry_dirty_i | cmoh_flush_req_inval_q);

                    dir_updt_set_o   = cmoh_flush_req_set_q;
                    dir_updt_way_o   = cmoh_flush_req_way_q;
                    dir_updt_valid_o = ~cmoh_flush_req_inval_q;
                    dir_updt_wback_o = ~cmoh_flush_req_inval_q & dir_check_entry_wback_i;
                    dir_updt_dirty_o = 1'b0;
                    dir_updt_fetch_o = 1'b0;
                    dir_updt_tag_o   = dir_check_entry_tag_i;
                    cmoh_flush_req_set = cmoh_flush_req_set_q;
                    cmoh_flush_req_way = cmoh_flush_req_way_q;
                    cmoh_flush_req_tag = dir_check_entry_tag_i;
                end

                //  Make sure that all requests have been processed
                if (flush_empty_i && !flush_alloc_o) begin
                    core_rsp_send_d = core_rsp_rok;
                    cmoh_fsm_d = CMOH_IDLE;
                end
            end
            CMOH_FLUSH_NLINE_FIRST: begin
                if (HPDcacheCfg.u.wbEn) begin
                    if (cmoh_flush_req_wok) begin
                        dir_check_nline_o = 1'b1;
                        cmoh_flush_req_valid_d = 1'b1;
                        cmoh_fsm_d = CMOH_FLUSH_NLINE_NEXT;
                    end
                end else if (cmoh_flush_req_inval_q) begin
                    cmoh_fsm_d = CMOH_INVAL_CHECK_NLINE;
                end else begin
                    core_rsp_send_d = core_rsp_rok;
                    cmoh_fsm_d = CMOH_IDLE;
                end
            end
            CMOH_FLUSH_NLINE_NEXT: begin
                cmoh_flush_req_valid_d = 1'b0;
                if (cmoh_flush_req_valid_q) begin
                    /* FIXME this adds a DIR to DIR timing path. We should probably delay the
                     *       invalidation of one cycle to ease the timing closure */
                    dir_updt_o       = cmoh_dir_check_nline_hit;
                    dir_updt_set_o   = cmoh_set;
                    dir_updt_way_o   = dir_check_nline_hit_way_i;
                    dir_updt_valid_o = ~cmoh_flush_req_inval_q;
                    dir_updt_wback_o = ~cmoh_flush_req_inval_q & dir_check_nline_wback_i;
                    dir_updt_dirty_o = 1'b0;
                    dir_updt_fetch_o = 1'b0;
                    dir_updt_tag_o   = cmoh_tag;
                    cmoh_flush_req_set = cmoh_set;
                    cmoh_flush_req_tag = cmoh_tag;
                    cmoh_flush_req_way = dir_check_nline_hit_way_i;
                end

                //  Make sure that all requests have been processed
                if (flush_empty_i && !flush_alloc_o) begin
                    core_rsp_send_d = core_rsp_rok;
                    cmoh_fsm_d = CMOH_IDLE;
                end
            end
        endcase
    end

    assign cmoh_set_last = (cmoh_set_q == hpdcache_set_t'(HPDcacheCfg.u.sets - 1));

    always_comb
    begin : set_incr_comb
        cmoh_set_d = cmoh_set_q;
        if (cmoh_set_reset) begin
            cmoh_set_d = '0;
        end else if (cmoh_set_incr) begin
            cmoh_set_d = cmoh_set_last ? '0 : cmoh_set_q + 1;
        end
    end

    assign cmoh_way_last = cmoh_way_q[HPDcacheCfg.u.ways - 1];

    always_comb
    begin : way_incr_comb
        cmoh_way_d = cmoh_way_q;
        if (cmoh_way_reset) begin
            cmoh_way_d = hpdcache_way_vector_t'(1);
        end else if (cmoh_way_incr) begin
            cmoh_way_d = cmoh_way_last ?
                hpdcache_way_vector_t'(1) : {cmoh_way_q[0 +: HPDcacheCfg.u.ways-1], 1'b0};
        end
    end
//  }}}

//  CMO request handler set state
//  {{{
    always_ff @(posedge clk_i or negedge rst_ni)
    begin
        if (!rst_ni) begin
            core_rsp_send_q <= 1'b0;
            cmoh_fsm_q      <= CMOH_IDLE;
        end else begin
            core_rsp_send_q <= core_rsp_send_d;
            cmoh_fsm_q      <= cmoh_fsm_d;
        end
    end

    always_ff @(posedge clk_i)
    begin
        cmoh_op_q              <= cmoh_op_d;
        cmoh_addr_q            <= cmoh_addr_d;
        cmoh_way_q             <= cmoh_way_d;
        cmoh_set_q             <= cmoh_set_d;
        cmoh_flush_req_valid_q <= cmoh_flush_req_valid_d;
        cmoh_flush_req_set_q   <= cmoh_flush_req_set_d;
        cmoh_flush_req_way_q   <= cmoh_flush_req_way_d;
        cmoh_flush_req_inval_q <= cmoh_flush_req_inval_d;
    end
//  }}}

//  CMO internal components
//  {{{
    typedef struct packed {
        hpdcache_nline_t      nline;
        hpdcache_way_vector_t way;
    } cmoh_flush_req_t;

    if (HPDcacheCfg.u.wbEn) begin : gen_cmo_flush_fifo
        cmoh_flush_req_t cmoh_flush_req_wdata, cmoh_flush_req_rdata;

        always_comb
        begin : cmoh_flush_req_w_comb
            cmoh_flush_req_w = 1'b0;
            if (cmoh_flush_req_valid_q) begin
                unique case (cmoh_fsm_q)
                    CMOH_FLUSH_ALL_NEXT, CMOH_FLUSH_ALL_LAST:
                        cmoh_flush_req_w = dir_check_entry_valid_i & dir_check_entry_dirty_i;
                    CMOH_FLUSH_NLINE_NEXT:
                        cmoh_flush_req_w = cmoh_dir_check_nline_hit & dir_check_nline_dirty_i;
                endcase
            end
        end

        assign cmoh_flush_req_wdata = '{
            nline: {cmoh_flush_req_tag, cmoh_flush_req_set},
            way  :  cmoh_flush_req_way
        };

        hpdcache_fifo_reg #(
            .FIFO_DEPTH  (3),
            .FEEDTHROUGH (1'b1),
            .fifo_data_t (cmoh_flush_req_t)
        ) flush_req_fifo_i(
            .clk_i,
            .rst_ni,
            .w_i     (cmoh_flush_req_w),
            .wok_o   (cmoh_flush_req_wok),
            .wdata_i (cmoh_flush_req_wdata),
            .r_i     (flush_alloc_ready_i),
            .rok_o   (flush_alloc_o),
            .rdata_o (cmoh_flush_req_rdata)
        );

        assign flush_alloc_nline_o = cmoh_flush_req_rdata.nline;
        assign flush_alloc_way_o   = cmoh_flush_req_rdata.way;
    end else begin : gen_cmo_no_flush_fifo
        assign cmoh_flush_req_w    = 1'b0;
        assign cmoh_flush_req_wok  = 1'b1;
        assign flush_alloc_o       = 1'b0;
        assign flush_alloc_nline_o = '0;
        assign flush_alloc_way_o   = '0;
    end
//  }}}

//  Assertions
//  {{{
`ifndef HPDCACHE_ASSERT_OFF
    assert property (@(posedge clk_i) disable iff (!rst_ni)
            req_valid_i -> $onehot({req_op_i.is_fence,
                                    req_op_i.is_inval_by_nline,
                                    req_op_i.is_inval_all,
                                    req_op_i.is_flush_by_nline,
                                    req_op_i.is_flush_all,
                                    req_op_i.is_flush_inval_by_nline,
                                    req_op_i.is_flush_inval_all})) else
                    $error("cmo_handler: invalid request");

    assert property (@(posedge clk_i) disable iff (!rst_ni)
            req_valid_i -> (cmoh_fsm_q == CMOH_IDLE)) else
                    $error("cmo_handler: new request received while busy");
`endif
//  }}}

endmodule
