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
 *  Creation Date : April, 2021
 *  Description   : HPDcache top
 *  History       :
 */
`include "hpdcache_typedef.svh"

module hpdcache
import hpdcache_pkg::*;
    //  Parameters
    //  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    parameter type wbuf_timecnt_t = logic,

    //  Request Interface Definitions
    //  {{{
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_data_word_t = logic,
    parameter type hpdcache_data_be_t = logic,
    parameter type hpdcache_req_offset_t = logic,
    parameter type hpdcache_req_data_t = logic,
    parameter type hpdcache_req_be_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_tid_t = logic,
    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic,
    //  }}}

    //  Memory Interface Definitions
    //  {{{
    parameter type hpdcache_mem_addr_t = logic,
    parameter type hpdcache_mem_id_t = logic,
    parameter type hpdcache_mem_data_t = logic,
    parameter type hpdcache_mem_be_t = logic,
    parameter type hpdcache_mem_req_t = logic,
    parameter type hpdcache_mem_req_w_t = logic,
    parameter type hpdcache_mem_resp_r_t = logic,
    parameter type hpdcache_mem_resp_w_t = logic
    //  }}}
)
    //  }}}

    //  Ports
    //  {{{
(
    //      Clock and reset signals
    input  logic                          clk_i,
    input  logic                          rst_ni,

    //      Force the write buffer to send all pending writes
    input  logic                          wbuf_flush_i,

    //      Core request interface
    //         1st cycle
    input  logic                          core_req_valid_i [HPDcacheCfg.u.nRequesters],
    output logic                          core_req_ready_o [HPDcacheCfg.u.nRequesters],
    input  hpdcache_req_t                 core_req_i       [HPDcacheCfg.u.nRequesters],
    //         2nd cycle
    input  logic                          core_req_abort_i [HPDcacheCfg.u.nRequesters],
    input  hpdcache_tag_t                 core_req_tag_i   [HPDcacheCfg.u.nRequesters],
    input  hpdcache_pma_t                 core_req_pma_i   [HPDcacheCfg.u.nRequesters],

    //      Core response interface
    output logic                          core_rsp_valid_o [HPDcacheCfg.u.nRequesters],
    output hpdcache_rsp_t                 core_rsp_o       [HPDcacheCfg.u.nRequesters],

    //      Read / Invalidation memory interface
    input  logic                          mem_req_read_ready_i,
    output logic                          mem_req_read_valid_o,
    output hpdcache_mem_req_t             mem_req_read_o,

    output logic                          mem_resp_read_ready_o,
    input  logic                          mem_resp_read_valid_i,
    input  hpdcache_mem_resp_r_t          mem_resp_read_i,
`ifdef HPDCACHE_OPENPITON
    input  logic                          mem_resp_read_inval_i,
    input  hpdcache_nline_t               mem_resp_read_inval_nline_i,
`endif

    //      Write memory interface
    input  logic                          mem_req_write_ready_i,
    output logic                          mem_req_write_valid_o,
    output hpdcache_mem_req_t             mem_req_write_o,

    input  logic                          mem_req_write_data_ready_i,
    output logic                          mem_req_write_data_valid_o,
    output hpdcache_mem_req_w_t           mem_req_write_data_o,

    output logic                          mem_resp_write_ready_o,
    input  logic                          mem_resp_write_valid_i,
    input  hpdcache_mem_resp_w_t          mem_resp_write_i,

    //      Performance events
    output logic                          evt_cache_write_miss_o,
    output logic                          evt_cache_read_miss_o,
    output logic                          evt_uncached_req_o,
    output logic                          evt_cmo_req_o,
    output logic                          evt_write_req_o,
    output logic                          evt_read_req_o,
    output logic                          evt_prefetch_req_o,
    output logic                          evt_req_on_hold_o,
    output logic                          evt_rtab_rollback_o,
    output logic                          evt_stall_refill_o,
    output logic                          evt_stall_o,

    //      Status interface
    output logic                          wbuf_empty_o,

    //      Configuration interface
    input  logic                          cfg_enable_i,
    input  wbuf_timecnt_t                 cfg_wbuf_threshold_i,
    input  logic                          cfg_wbuf_reset_timecnt_on_write_i,
    input  logic                          cfg_wbuf_sequential_waw_i,
    input  logic                          cfg_wbuf_inhibit_write_coalescing_i,
    input  logic                          cfg_prefetch_updt_plru_i,
    input  logic                          cfg_error_on_cacheable_amo_i,
    input  logic                          cfg_rtab_single_entry_i,
    input  logic                          cfg_default_wb_i
);
    //  }}}

    //  Declaration of internal types
    //  {{{
    typedef logic [HPDcacheCfg.u.paWidth-1:0] hpdcache_req_addr_t;
    typedef logic [HPDcacheCfg.nlineWidth-1:0] hpdcache_nline_t;
    typedef logic [HPDcacheCfg.setWidth-1:0] hpdcache_set_t;
    typedef logic [HPDcacheCfg.clOffsetWidth-1:0] hpdcache_offset_t;
    typedef logic unsigned [HPDcacheCfg.clWordIdxWidth-1:0] hpdcache_word_t;
    typedef logic unsigned [HPDcacheCfg.u.ways-1:0] hpdcache_way_vector_t;
    typedef logic unsigned [HPDcacheCfg.wayIndexWidth-1:0] hpdcache_way_t;

    //  Cache Directory entry definition
    //  {{{
    typedef struct packed {
        //  Cacheline state
        //  Encoding: {valid, wb, dirty, fetch}
        //            {0,X,X,0}: Invalid
        //            {0,X,X,1}: Invalid and Fetching
        //            {1,X,X,1}: Valid and Fetching (cacheline being replaced is accessible)
        //            {1,0,0,0}: Write-through
        //            {1,1,0,0}: Write-back (clean)
        //            {1,1,1,0}: Write-back (dirty)
        //  {{{
        logic valid; //  valid cacheline
        logic wback; //  cacheline in write-back mode
        logic dirty; //  cacheline is locally modified (memory is obsolete)
        logic fetch; //  cacheline is reserved for a new cacheline being fetched
        //  }}}

        //  Cacheline address tag
        //  {{{
        hpdcache_tag_t tag;
        //  }}}
    } hpdcache_dir_entry_t;
    //  }}}

    typedef hpdcache_data_word_t [HPDcacheCfg.u.accessWords-1:0] hpdcache_access_data_t;
    typedef hpdcache_data_be_t [HPDcacheCfg.u.accessWords-1:0] hpdcache_access_be_t;

    typedef hpdcache_req_addr_t wbuf_addr_t;
    typedef hpdcache_req_data_t wbuf_data_t;
    typedef hpdcache_req_be_t wbuf_be_t;
    //  }}}

    //  Declaration of internal signals
    //  {{{
    logic                  refill_req_valid;
    logic                  refill_req_ready;
    logic                  refill_is_error;
    logic                  refill_busy;
    logic                  refill_updt_sel_victim;
    hpdcache_set_t         refill_set;
    hpdcache_way_vector_t  refill_way;
    hpdcache_dir_entry_t   refill_dir_entry;
    logic                  refill_write_dir;
    logic                  refill_write_data;
    hpdcache_word_t        refill_word;
    hpdcache_access_data_t refill_data;
    logic                  refill_core_rsp_valid;
    hpdcache_rsp_t         refill_core_rsp;
    hpdcache_nline_t       refill_nline;
    logic                  refill_updt_rtab;

    logic                  inval_check_dir;
    logic                  inval_write_dir;
    hpdcache_nline_t       inval_nline;
    logic                  inval_hit;

    logic                  miss_mshr_empty;
    logic                  miss_mshr_check;
    hpdcache_req_offset_t  miss_mshr_check_offset;
    hpdcache_nline_t       miss_mshr_check_nline;
    logic                  miss_mshr_hit;
    logic                  miss_mshr_alloc_cs;
    logic                  miss_mshr_alloc;
    logic                  miss_mshr_alloc_ready;
    logic                  miss_mshr_alloc_full;
    hpdcache_nline_t       miss_mshr_alloc_nline;
    hpdcache_req_tid_t     miss_mshr_alloc_tid;
    hpdcache_req_sid_t     miss_mshr_alloc_sid;
    hpdcache_word_t        miss_mshr_alloc_word;
    hpdcache_way_vector_t  miss_mshr_alloc_victim_way;
    logic                  miss_mshr_alloc_need_rsp;
    logic                  miss_mshr_alloc_is_prefetch;
    logic                  miss_mshr_alloc_wback;

    logic                  wbuf_flush_all;
    logic                  wbuf_write;
    logic                  wbuf_write_ready;
    wbuf_addr_t            wbuf_write_addr;
    wbuf_data_t            wbuf_write_data;
    wbuf_be_t              wbuf_write_be;
    logic                  wbuf_write_uncacheable;
    logic                  wbuf_read_hit;
    logic                  wbuf_read_flush_hit;
    hpdcache_req_addr_t    wbuf_rtab_addr;
    logic                  wbuf_rtab_is_read;
    logic                  wbuf_rtab_hit_open;
    logic                  wbuf_rtab_hit_pend;
    logic                  wbuf_rtab_hit_sent;
    logic                  wbuf_rtab_not_ready;

    logic                  uc_ready;
    logic                  uc_req_valid;
    hpdcache_uc_op_t       uc_req_op;
    hpdcache_req_addr_t    uc_req_addr;
    hpdcache_req_size_t    uc_req_size;
    hpdcache_req_data_t    uc_req_data;
    hpdcache_req_be_t      uc_req_be;
    logic                  uc_req_uncacheable;
    hpdcache_req_sid_t     uc_req_sid;
    hpdcache_req_tid_t     uc_req_tid;
    logic                  uc_req_need_rsp;
    logic                  uc_wbuf_flush_all;
    logic                  uc_dir_amo_match;
    hpdcache_set_t         uc_dir_amo_match_set;
    hpdcache_tag_t         uc_dir_amo_match_tag;
    logic                  uc_dir_amo_updt_sel_victim;
    hpdcache_way_vector_t  uc_dir_amo_hit_way;
    logic                  uc_data_amo_write;
    logic                  uc_data_amo_write_enable;
    hpdcache_set_t         uc_data_amo_write_set;
    hpdcache_req_size_t    uc_data_amo_write_size;
    hpdcache_word_t        uc_data_amo_write_word;
    hpdcache_req_data_t    uc_data_amo_write_data;
    hpdcache_req_be_t      uc_data_amo_write_be;
    logic                  uc_lrsc_snoop;
    hpdcache_req_addr_t    uc_lrsc_snoop_addr;
    hpdcache_req_size_t    uc_lrsc_snoop_size;
    logic                  uc_core_rsp_ready;
    logic                  uc_core_rsp_valid;
    hpdcache_rsp_t         uc_core_rsp;

    logic                  cmo_req_valid;
    logic                  cmo_ready;
    hpdcache_cmoh_op_t     cmo_req_op;
    hpdcache_req_addr_t    cmo_req_addr;
    hpdcache_req_sid_t     cmo_req_sid;
    hpdcache_req_tid_t     cmo_req_tid;
    hpdcache_req_data_t    cmo_req_wdata;
    logic                  cmo_req_need_rsp;
    logic                  cmo_wbuf_flush_all;
    logic                  cmo_dir_check_nline;
    hpdcache_set_t         cmo_dir_check_nline_set;
    hpdcache_tag_t         cmo_dir_check_nline_tag;
    hpdcache_way_vector_t  cmo_dir_check_nline_hit_way;
    logic                  cmo_dir_check_nline_wback;
    logic                  cmo_dir_check_nline_dirty;
    logic                  cmo_dir_check_entry;
    hpdcache_set_t         cmo_dir_check_entry_set;
    hpdcache_way_vector_t  cmo_dir_check_entry_way;
    logic                  cmo_dir_check_entry_valid;
    logic                  cmo_dir_check_entry_wback;
    logic                  cmo_dir_check_entry_dirty;
    hpdcache_tag_t         cmo_dir_check_entry_tag;
    logic                  cmo_dir_updt;
    hpdcache_set_t         cmo_dir_updt_set;
    hpdcache_way_vector_t  cmo_dir_updt_way;
    logic                  cmo_dir_updt_valid;
    logic                  cmo_dir_updt_wback;
    logic                  cmo_dir_updt_dirty;
    logic                  cmo_dir_updt_fetch;
    hpdcache_tag_t         cmo_dir_updt_tag;
    logic                  cmo_wait;
    logic                  cmo_flush_alloc;
    hpdcache_nline_t       cmo_flush_alloc_nline;
    hpdcache_way_vector_t  cmo_flush_alloc_way;
    logic                  cmo_core_rsp_ready;
    logic                  cmo_core_rsp_valid;
    hpdcache_rsp_t         cmo_core_rsp;

    logic                  flush_empty;
    logic                  flush_busy;
    hpdcache_nline_t       flush_check_nline;
    logic                  flush_check_hit;
    logic                  flush_alloc;
    logic                  flush_alloc_ready;
    hpdcache_nline_t       flush_alloc_nline;
    hpdcache_way_vector_t  flush_alloc_way;
    logic                  flush_data_read;
    hpdcache_set_t         flush_data_read_set;
    hpdcache_word_t        flush_data_read_word;
    hpdcache_way_vector_t  flush_data_read_way;
    hpdcache_access_data_t flush_data_read_data;
    logic                  flush_ack;
    hpdcache_nline_t       flush_ack_nline;

    logic                  ctrl_flush_alloc;
    hpdcache_nline_t       ctrl_flush_alloc_nline;
    hpdcache_way_vector_t  ctrl_flush_alloc_way;

    logic                  rtab_empty;
    logic                  ctrl_empty;

    logic                  core_rsp_valid;
    hpdcache_rsp_t         core_rsp;

    logic                  arb_req_valid;
    logic                  arb_req_ready;
    hpdcache_req_t         arb_req;
    logic                  arb_abort;
    hpdcache_tag_t         arb_tag;
    hpdcache_pma_t         arb_pma;

    logic                  mem_req_read_miss_ready;
    logic                  mem_req_read_miss_valid;
    hpdcache_mem_req_t     mem_req_read_miss;

    logic                  mem_resp_read_miss_ready;
    logic                  mem_resp_read_miss_valid;
    hpdcache_mem_resp_r_t  mem_resp_read_miss;
    logic                  mem_resp_read_miss_inval;
    hpdcache_nline_t       mem_resp_read_miss_inval_nline;

    logic                  mem_req_read_uc_ready;
    logic                  mem_req_read_uc_valid;
    hpdcache_mem_req_t     mem_req_read_uc;

    logic                  mem_resp_read_uc_ready;
    logic                  mem_resp_read_uc_valid;
    hpdcache_mem_resp_r_t  mem_resp_read_uc;

    logic                  mem_req_write_wbuf_ready;
    logic                  mem_req_write_wbuf_valid;
    hpdcache_mem_req_t     mem_req_write_wbuf;

    logic                  mem_req_write_wbuf_data_ready;
    logic                  mem_req_write_wbuf_data_valid;
    hpdcache_mem_req_w_t   mem_req_write_wbuf_data;

    logic                  mem_resp_write_wbuf_ready;
    logic                  mem_resp_write_wbuf_valid;
    hpdcache_mem_resp_w_t  mem_resp_write_wbuf;

    logic                  mem_req_write_flush_ready;
    logic                  mem_req_write_flush_valid;
    hpdcache_mem_req_t     mem_req_write_flush;

    logic                  mem_req_write_flush_data_ready;
    logic                  mem_req_write_flush_data_valid;
    hpdcache_mem_req_w_t   mem_req_write_flush_data;

    logic                  mem_resp_write_flush_ready;
    logic                  mem_resp_write_flush_valid;
    hpdcache_mem_resp_w_t  mem_resp_write_flush;

    logic                  mem_req_write_uc_ready;
    logic                  mem_req_write_uc_valid;
    hpdcache_mem_req_t     mem_req_write_uc;

    logic                  mem_req_write_uc_data_ready;
    logic                  mem_req_write_uc_data_valid;
    hpdcache_mem_req_w_t   mem_req_write_uc_data;

    logic                  mem_resp_write_uc_ready;
    logic                  mem_resp_write_uc_valid;
    hpdcache_mem_resp_w_t  mem_resp_write_uc;

    logic                  cfg_default_wb;

    localparam logic [HPDcacheCfg.u.memIdWidth-1:0] HPDCACHE_UC_READ_ID =
        {HPDcacheCfg.u.memIdWidth{1'b1}};
    localparam logic [HPDcacheCfg.u.memIdWidth-1:0] HPDCACHE_UC_WRITE_ID =
        {HPDcacheCfg.u.memIdWidth{1'b1}};
    //  }}}

    //  Requesters arbiter
    //  {{{
    hpdcache_core_arbiter #(
        .HPDcacheCfg                        (HPDcacheCfg),
        .hpdcache_tag_t                     (hpdcache_tag_t),
        .hpdcache_req_t                     (hpdcache_req_t),
        .hpdcache_rsp_t                     (hpdcache_rsp_t)
    ) core_req_arbiter_i (
        .clk_i,
        .rst_ni,

        .core_req_valid_i,
        .core_req_ready_o,
        .core_req_i,
        .core_req_abort_i,
        .core_req_tag_i,
        .core_req_pma_i,

        .core_rsp_valid_i                   (core_rsp_valid),
        .core_rsp_i                         (core_rsp),
        .core_rsp_valid_o,
        .core_rsp_o,

        .arb_req_valid_o                    (arb_req_valid),
        .arb_req_ready_i                    (arb_req_ready),
        .arb_req_o                          (arb_req),
        .arb_abort_o                        (arb_abort),
        .arb_tag_o                          (arb_tag),
        .arb_pma_o                          (arb_pma)
    );
    //  }}}

    //  HPDcache controller
    //  {{{
    if (HPDcacheCfg.u.wtEn && HPDcacheCfg.u.wbEn) begin : gen_cfg_default_wt_wb
        assign cfg_default_wb = cfg_default_wb_i;
    end else if (HPDcacheCfg.u.wtEn) begin : gen_cfg_default_wt
        assign cfg_default_wb = 1'b0;
    end else if (HPDcacheCfg.u.wbEn) begin : gen_cfg_default_wb
        assign cfg_default_wb = 1'b1;
    end

    hpdcache_ctrl #(
        .HPDcacheCfg                        (HPDcacheCfg),
        .hpdcache_nline_t                   (hpdcache_nline_t),
        .hpdcache_tag_t                     (hpdcache_tag_t),
        .hpdcache_set_t                     (hpdcache_set_t),
        .hpdcache_word_t                    (hpdcache_word_t),
        .hpdcache_data_word_t               (hpdcache_data_word_t),
        .hpdcache_data_be_t                 (hpdcache_data_be_t),
        .hpdcache_dir_entry_t               (hpdcache_dir_entry_t),
        .hpdcache_way_vector_t              (hpdcache_way_vector_t),
        .hpdcache_way_t                     (hpdcache_way_t),
        .wbuf_addr_t                        (wbuf_addr_t),
        .wbuf_data_t                        (wbuf_data_t),
        .wbuf_be_t                          (wbuf_be_t),
        .hpdcache_access_data_t             (hpdcache_access_data_t),
        .hpdcache_access_be_t               (hpdcache_access_be_t),
        .hpdcache_req_addr_t                (hpdcache_req_addr_t),
        .hpdcache_req_offset_t              (hpdcache_req_offset_t),
        .hpdcache_req_tid_t                 (hpdcache_req_tid_t),
        .hpdcache_req_sid_t                 (hpdcache_req_sid_t),
        .hpdcache_req_data_t                (hpdcache_req_data_t),
        .hpdcache_req_be_t                  (hpdcache_req_be_t),
        .hpdcache_req_t                     (hpdcache_req_t),
        .hpdcache_rsp_t                     (hpdcache_rsp_t)
    ) hpdcache_ctrl_i(
        .clk_i,
        .rst_ni,

        .core_req_valid_i                   (arb_req_valid),
        .core_req_ready_o                   (arb_req_ready),
        .core_req_i                         (arb_req),
        .core_req_abort_i                   (arb_abort),
        .core_req_tag_i                     (arb_tag),
        .core_req_pma_i                     (arb_pma),

        .core_rsp_valid_o                   (core_rsp_valid),
        .core_rsp_o                         (core_rsp),

        .wbuf_flush_i,

        .cachedir_hit_o                     (/* unused */),

        .st0_mshr_check_o                   (miss_mshr_check),
        .st0_mshr_check_offset_o            (miss_mshr_check_offset),
        .st1_mshr_check_nline_o             (miss_mshr_check_nline),
        .st1_mshr_hit_i                     (miss_mshr_hit),
        .st1_mshr_alloc_ready_i             (miss_mshr_alloc_ready),
        .st1_mshr_alloc_full_i              (miss_mshr_alloc_full),
        .st2_mshr_alloc_o                   (miss_mshr_alloc),
        .st2_mshr_alloc_cs_o                (miss_mshr_alloc_cs),
        .st2_mshr_alloc_nline_o             (miss_mshr_alloc_nline),
        .st2_mshr_alloc_tid_o               (miss_mshr_alloc_tid),
        .st2_mshr_alloc_sid_o               (miss_mshr_alloc_sid),
        .st2_mshr_alloc_word_o              (miss_mshr_alloc_word),
        .st2_mshr_alloc_victim_way_o        (miss_mshr_alloc_victim_way),
        .st2_mshr_alloc_need_rsp_o          (miss_mshr_alloc_need_rsp),
        .st2_mshr_alloc_is_prefetch_o       (miss_mshr_alloc_is_prefetch),
        .st2_mshr_alloc_wback_o             (miss_mshr_alloc_wback),

        .refill_req_valid_i                 (refill_req_valid),
        .refill_req_ready_o                 (refill_req_ready),
        .refill_is_error_i                  (refill_is_error),
        .refill_busy_i                      (refill_busy),
        .refill_updt_sel_victim_i           (refill_updt_sel_victim),
        .refill_set_i                       (refill_set),
        .refill_way_i                       (refill_way),
        .refill_dir_entry_i                 (refill_dir_entry),
        .refill_write_dir_i                 (refill_write_dir),
        .refill_write_data_i                (refill_write_data),
        .refill_word_i                      (refill_word),
        .refill_data_i                      (refill_data),
        .refill_core_rsp_valid_i            (refill_core_rsp_valid),
        .refill_core_rsp_i                  (refill_core_rsp),
        .refill_nline_i                     (refill_nline),
        .refill_updt_rtab_i                 (refill_updt_rtab),

        .flush_busy_i                       (flush_busy),
        .flush_check_nline_o                (flush_check_nline),
        .flush_check_hit_i                  (flush_check_hit),
        .flush_alloc_o                      (ctrl_flush_alloc),
        .flush_alloc_ready_i                (flush_alloc_ready),
        .flush_alloc_nline_o                (ctrl_flush_alloc_nline),
        .flush_alloc_way_o                  (ctrl_flush_alloc_way),
        .flush_data_read_i                  (flush_data_read),
        .flush_data_read_set_i              (flush_data_read_set),
        .flush_data_read_word_i             (flush_data_read_word),
        .flush_data_read_way_i              (flush_data_read_way),
        .flush_data_read_data_o             (flush_data_read_data),
        .flush_ack_i                        (flush_ack),
        .flush_ack_nline_i                  (flush_ack_nline),

        .inval_check_dir_i                  (inval_check_dir),
        .inval_write_dir_i                  (inval_write_dir),
        .inval_nline_i                      (inval_nline),
        .inval_hit_o                        (inval_hit),

        .wbuf_empty_i                       (wbuf_empty_o),
        .wbuf_flush_all_o                   (wbuf_flush_all),
        .wbuf_write_o                       (wbuf_write),
        .wbuf_write_ready_i                 (wbuf_write_ready),
        .wbuf_write_addr_o                  (wbuf_write_addr),
        .wbuf_write_data_o                  (wbuf_write_data),
        .wbuf_write_be_o                    (wbuf_write_be),
        .wbuf_write_uncacheable_o           (wbuf_write_uncacheable),
        .wbuf_read_hit_i                    (wbuf_read_hit),
        .wbuf_read_flush_hit_o              (wbuf_read_flush_hit),
        .wbuf_rtab_addr_o                   (wbuf_rtab_addr),
        .wbuf_rtab_is_read_o                (wbuf_rtab_is_read),
        .wbuf_rtab_hit_open_i               (wbuf_rtab_hit_open),
        .wbuf_rtab_hit_pend_i               (wbuf_rtab_hit_pend),
        .wbuf_rtab_hit_sent_i               (wbuf_rtab_hit_sent),
        .wbuf_rtab_not_ready_i              (wbuf_rtab_not_ready),

        .uc_busy_i                          (~uc_ready),
        .uc_lrsc_snoop_o                    (uc_lrsc_snoop),
        .uc_lrsc_snoop_addr_o               (uc_lrsc_snoop_addr),
        .uc_lrsc_snoop_size_o               (uc_lrsc_snoop_size),
        .uc_req_valid_o                     (uc_req_valid),
        .uc_req_op_o                        (uc_req_op),
        .uc_req_addr_o                      (uc_req_addr),
        .uc_req_size_o                      (uc_req_size),
        .uc_req_data_o                      (uc_req_data),
        .uc_req_be_o                        (uc_req_be),
        .uc_req_uc_o                        (uc_req_uncacheable),
        .uc_req_sid_o                       (uc_req_sid),
        .uc_req_tid_o                       (uc_req_tid),
        .uc_req_need_rsp_o                  (uc_req_need_rsp),
        .uc_wbuf_flush_all_i                (uc_wbuf_flush_all),
        .uc_dir_amo_match_i                 (uc_dir_amo_match),
        .uc_dir_amo_match_set_i             (uc_dir_amo_match_set),
        .uc_dir_amo_match_tag_i             (uc_dir_amo_match_tag),
        .uc_dir_amo_updt_sel_victim_i       (uc_dir_amo_updt_sel_victim),
        .uc_dir_amo_hit_way_o               (uc_dir_amo_hit_way),
        .uc_data_amo_write_i                (uc_data_amo_write),
        .uc_data_amo_write_enable_i         (uc_data_amo_write_enable),
        .uc_data_amo_write_set_i            (uc_data_amo_write_set),
        .uc_data_amo_write_size_i           (uc_data_amo_write_size),
        .uc_data_amo_write_word_i           (uc_data_amo_write_word),
        .uc_data_amo_write_data_i           (uc_data_amo_write_data),
        .uc_data_amo_write_be_i             (uc_data_amo_write_be),
        .uc_core_rsp_ready_o                (uc_core_rsp_ready),
        .uc_core_rsp_valid_i                (uc_core_rsp_valid),
        .uc_core_rsp_i                      (uc_core_rsp),

        .cmo_busy_i                         (~cmo_ready),
        .cmo_wait_i                         (cmo_wait),
        .cmo_req_valid_o                    (cmo_req_valid),
        .cmo_req_op_o                       (cmo_req_op),
        .cmo_req_addr_o                     (cmo_req_addr),
        .cmo_req_wdata_o                    (cmo_req_wdata),
        .cmo_req_sid_o                      (cmo_req_sid),
        .cmo_req_tid_o                      (cmo_req_tid),
        .cmo_req_need_rsp_o                 (cmo_req_need_rsp),
        .cmo_wbuf_flush_all_i               (cmo_wbuf_flush_all),
        .cmo_dir_check_nline_i              (cmo_dir_check_nline),
        .cmo_dir_check_nline_set_i          (cmo_dir_check_nline_set),
        .cmo_dir_check_nline_tag_i          (cmo_dir_check_nline_tag),
        .cmo_dir_check_nline_hit_way_o      (cmo_dir_check_nline_hit_way),
        .cmo_dir_check_nline_wback_o        (cmo_dir_check_nline_wback),
        .cmo_dir_check_nline_dirty_o        (cmo_dir_check_nline_dirty),
        .cmo_dir_check_entry_i              (cmo_dir_check_entry),
        .cmo_dir_check_entry_set_i          (cmo_dir_check_entry_set),
        .cmo_dir_check_entry_way_i          (cmo_dir_check_entry_way),
        .cmo_dir_check_entry_valid_o        (cmo_dir_check_entry_valid),
        .cmo_dir_check_entry_wback_o        (cmo_dir_check_entry_wback),
        .cmo_dir_check_entry_dirty_o        (cmo_dir_check_entry_dirty),
        .cmo_dir_check_entry_tag_o          (cmo_dir_check_entry_tag),
        .cmo_dir_updt_i                     (cmo_dir_updt),
        .cmo_dir_updt_set_i                 (cmo_dir_updt_set),
        .cmo_dir_updt_way_i                 (cmo_dir_updt_way),
        .cmo_dir_updt_valid_i               (cmo_dir_updt_valid),
        .cmo_dir_updt_wback_i               (cmo_dir_updt_wback),
        .cmo_dir_updt_dirty_i               (cmo_dir_updt_dirty),
        .cmo_dir_updt_fetch_i               (cmo_dir_updt_fetch),
        .cmo_dir_updt_tag_i                 (cmo_dir_updt_tag),
        .cmo_core_rsp_ready_o               (cmo_core_rsp_ready),
        .cmo_core_rsp_valid_i               (cmo_core_rsp_valid),
        .cmo_core_rsp_i                     (cmo_core_rsp),

        .rtab_empty_o                       (rtab_empty),
        .ctrl_empty_o                       (ctrl_empty),

        .cfg_enable_i,
        .cfg_prefetch_updt_plru_i,
        .cfg_rtab_single_entry_i,
        .cfg_default_wb_i                   (cfg_default_wb),

        .evt_cache_write_miss_o,
        .evt_cache_read_miss_o,
        .evt_uncached_req_o,
        .evt_cmo_req_o,
        .evt_write_req_o,
        .evt_read_req_o,
        .evt_prefetch_req_o,
        .evt_req_on_hold_o,
        .evt_rtab_rollback_o,
        .evt_stall_refill_o,
        .evt_stall_o
    );
    //  }}}

    //  HPDcache write-buffer
    //  {{{
    if (HPDcacheCfg.u.wtEn) begin : gen_wbuf
        hpdcache_wbuf #(
            .HPDcacheCfg                        (HPDcacheCfg),
            .wbuf_addr_t                        (wbuf_addr_t),
            .wbuf_timecnt_t                     (wbuf_timecnt_t),
            .hpdcache_mem_id_t                  (hpdcache_mem_id_t),
            .hpdcache_mem_req_t                 (hpdcache_mem_req_t),
            .hpdcache_mem_req_w_t               (hpdcache_mem_req_w_t),
            .hpdcache_mem_resp_w_t              (hpdcache_mem_resp_w_t)
        ) hpdcache_wbuf_i(
            .clk_i,
            .rst_ni,

            .empty_o                            (wbuf_empty_o),
            .full_o                             (/* unused */),
            .flush_all_i                        (wbuf_flush_all),

            .cfg_threshold_i                    (cfg_wbuf_threshold_i),
            .cfg_reset_timecnt_on_write_i       (cfg_wbuf_reset_timecnt_on_write_i),
            .cfg_sequential_waw_i               (cfg_wbuf_sequential_waw_i),
            .cfg_inhibit_write_coalescing_i     (cfg_wbuf_inhibit_write_coalescing_i),

            .write_i                            (wbuf_write),
            .write_ready_o                      (wbuf_write_ready),
            .write_addr_i                       (wbuf_write_addr),
            .write_data_i                       (wbuf_write_data),
            .write_be_i                         (wbuf_write_be),
            .write_uc_i                         (wbuf_write_uncacheable),

            .read_addr_i                        (wbuf_write_addr),
            .read_hit_o                         (wbuf_read_hit),
            .read_flush_hit_i                   (wbuf_read_flush_hit),

            .replay_addr_i                      (wbuf_rtab_addr),
            .replay_is_read_i                   (wbuf_rtab_is_read),
            .replay_open_hit_o                  (wbuf_rtab_hit_open),
            .replay_pend_hit_o                  (wbuf_rtab_hit_pend),
            .replay_sent_hit_o                  (wbuf_rtab_hit_sent),
            .replay_not_ready_o                 (wbuf_rtab_not_ready),

            .mem_req_write_ready_i              (mem_req_write_wbuf_ready),
            .mem_req_write_valid_o              (mem_req_write_wbuf_valid),
            .mem_req_write_o                    (mem_req_write_wbuf),

            .mem_req_write_data_ready_i         (mem_req_write_wbuf_data_ready),
            .mem_req_write_data_valid_o         (mem_req_write_wbuf_data_valid),
            .mem_req_write_data_o               (mem_req_write_wbuf_data),

            .mem_resp_write_ready_o             (mem_resp_write_wbuf_ready),
            .mem_resp_write_valid_i             (mem_resp_write_wbuf_valid),
            .mem_resp_write_i                   (mem_resp_write_wbuf)
        );
    end else begin : gen_no_wbuf
        //  The write-buffer behaves as a black-hole: consumes but do not produce data
        assign wbuf_empty_o                  = 1'b1;
        assign wbuf_write_ready              = 1'b1;
        assign wbuf_read_hit                 = 1'b0;
        assign wbuf_rtab_hit_open            = 1'b0;
        assign wbuf_rtab_hit_pend            = 1'b0;
        assign wbuf_rtab_hit_sent            = 1'b0;
        assign wbuf_rtab_not_ready           = 1'b0;
        assign mem_req_write_wbuf_valid      = 1'b0;
        assign mem_req_write_wbuf            = '{
            mem_req_command: HPDCACHE_MEM_READ,
            mem_req_atomic : HPDCACHE_MEM_ATOMIC_ADD,
            default        : '0
        };
        assign mem_req_write_wbuf_data_valid = 1'b0;
        assign mem_req_write_wbuf_data       = '0;
        assign mem_resp_write_wbuf_ready     = 1'b1;
    end
    //  }}}

    //  Miss handler
    //  {{{
    hpdcache_miss_handler #(
        .HPDcacheCfg                        (HPDcacheCfg),
        .hpdcache_nline_t                   (hpdcache_nline_t),
        .hpdcache_set_t                     (hpdcache_set_t),
        .hpdcache_tag_t                     (hpdcache_tag_t),
        .hpdcache_word_t                    (hpdcache_word_t),
        .hpdcache_way_vector_t              (hpdcache_way_vector_t),
        .hpdcache_way_t                     (hpdcache_way_t),
        .hpdcache_dir_entry_t               (hpdcache_dir_entry_t),
        .hpdcache_refill_data_t             (hpdcache_access_data_t),
        .hpdcache_req_data_t                (hpdcache_req_data_t),
        .hpdcache_req_offset_t              (hpdcache_req_offset_t),
        .hpdcache_req_sid_t                 (hpdcache_req_sid_t),
        .hpdcache_req_tid_t                 (hpdcache_req_tid_t),
        .hpdcache_req_t                     (hpdcache_req_t),
        .hpdcache_rsp_t                     (hpdcache_rsp_t),
        .hpdcache_mem_id_t                  (hpdcache_mem_id_t),
        .hpdcache_mem_req_t                 (hpdcache_mem_req_t),
        .hpdcache_mem_resp_r_t              (hpdcache_mem_resp_r_t)
    ) hpdcache_miss_handler_i(
        .clk_i,
        .rst_ni,

        .mshr_empty_o                       (miss_mshr_empty),
        .mshr_full_o                        (/* unused */),

        .cfg_prefetch_updt_sel_victim_i     (cfg_prefetch_updt_plru_i),

        .mshr_check_i                       (miss_mshr_check),
        .mshr_check_offset_i                (miss_mshr_check_offset),
        .mshr_check_nline_i                 (miss_mshr_check_nline),
        .mshr_check_hit_o                   (miss_mshr_hit),

        .mshr_alloc_ready_o                 (miss_mshr_alloc_ready),
        .mshr_alloc_i                       (miss_mshr_alloc),
        .mshr_alloc_cs_i                    (miss_mshr_alloc_cs),
        .mshr_alloc_nline_i                 (miss_mshr_alloc_nline),
        .mshr_alloc_full_o                  (miss_mshr_alloc_full),
        .mshr_alloc_tid_i                   (miss_mshr_alloc_tid),
        .mshr_alloc_sid_i                   (miss_mshr_alloc_sid),
        .mshr_alloc_word_i                  (miss_mshr_alloc_word),
        .mshr_alloc_victim_way_i            (miss_mshr_alloc_victim_way),
        .mshr_alloc_need_rsp_i              (miss_mshr_alloc_need_rsp),
        .mshr_alloc_is_prefetch_i           (miss_mshr_alloc_is_prefetch),
        .mshr_alloc_wback_i                 (miss_mshr_alloc_wback),

        .refill_req_ready_i                 (refill_req_ready),
        .refill_req_valid_o                 (refill_req_valid),
        .refill_is_error_o                  (refill_is_error),
        .refill_busy_o                      (refill_busy),
        .refill_updt_sel_victim_o           (refill_updt_sel_victim),
        .refill_set_o                       (refill_set),
        .refill_way_o                       (refill_way),
        .refill_dir_entry_o                 (refill_dir_entry),
        .refill_write_dir_o                 (refill_write_dir),
        .refill_write_data_o                (refill_write_data),
        .refill_data_o                      (refill_data),
        .refill_word_o                      (refill_word),
        .refill_nline_o                     (refill_nline),
        .refill_updt_rtab_o                 (refill_updt_rtab),

        .inval_check_dir_o                  (inval_check_dir),
        .inval_write_dir_o                  (inval_write_dir),
        .inval_nline_o                      (inval_nline),
        .inval_hit_i                        (inval_hit),

        .refill_core_rsp_valid_o            (refill_core_rsp_valid),
        .refill_core_rsp_o                  (refill_core_rsp),

        .mem_req_ready_i                    (mem_req_read_miss_ready),
        .mem_req_valid_o                    (mem_req_read_miss_valid),
        .mem_req_o                          (mem_req_read_miss),

        .mem_resp_ready_o                   (mem_resp_read_miss_ready),
        .mem_resp_valid_i                   (mem_resp_read_miss_valid),
        .mem_resp_i                         (mem_resp_read_miss),
        .mem_resp_inval_i                   (mem_resp_read_miss_inval),
        .mem_resp_inval_nline_i             (mem_resp_read_miss_inval_nline)
    );
    //  }}}

    //  Uncacheable request handler
    //  {{{
    hpdcache_uncached #(
        .HPDcacheCfg                   (HPDcacheCfg),
        .hpdcache_nline_t              (hpdcache_nline_t),
        .hpdcache_tag_t                (hpdcache_tag_t),
        .hpdcache_set_t                (hpdcache_set_t),
        .hpdcache_offset_t             (hpdcache_offset_t),
        .hpdcache_word_t               (hpdcache_word_t),
        .hpdcache_req_addr_t           (hpdcache_req_addr_t),
        .hpdcache_req_tid_t            (hpdcache_req_tid_t),
        .hpdcache_req_sid_t            (hpdcache_req_sid_t),
        .hpdcache_req_data_t           (hpdcache_req_data_t),
        .hpdcache_req_be_t             (hpdcache_req_be_t),
        .hpdcache_way_vector_t         (hpdcache_way_vector_t),
        .hpdcache_req_t                (hpdcache_req_t),
        .hpdcache_rsp_t                (hpdcache_rsp_t),
        .hpdcache_mem_id_t             (hpdcache_mem_id_t),
        .hpdcache_mem_req_t            (hpdcache_mem_req_t),
        .hpdcache_mem_req_w_t          (hpdcache_mem_req_w_t),
        .hpdcache_mem_resp_r_t         (hpdcache_mem_resp_r_t),
        .hpdcache_mem_resp_w_t         (hpdcache_mem_resp_w_t)
    ) hpdcache_uc_i(
        .clk_i,
        .rst_ni,

        .wbuf_empty_i                  (wbuf_empty_o),
        .mshr_empty_i                  (miss_mshr_empty),
        .rtab_empty_i                  (rtab_empty),
        .ctrl_empty_i                  (ctrl_empty),
        .flush_empty_i                 (flush_empty),

        .req_valid_i                   (uc_req_valid),
        .req_ready_o                   (uc_ready),
        .req_op_i                      (uc_req_op),
        .req_addr_i                    (uc_req_addr),
        .req_size_i                    (uc_req_size),
        .req_data_i                    (uc_req_data),
        .req_be_i                      (uc_req_be),
        .req_uc_i                      (uc_req_uncacheable),
        .req_sid_i                     (uc_req_sid),
        .req_tid_i                     (uc_req_tid),
        .req_need_rsp_i                (uc_req_need_rsp),

        .wbuf_flush_all_o              (uc_wbuf_flush_all),

        .dir_amo_match_o               (uc_dir_amo_match),
        .dir_amo_match_set_o           (uc_dir_amo_match_set),
        .dir_amo_match_tag_o           (uc_dir_amo_match_tag),
        .dir_amo_updt_sel_victim_o     (uc_dir_amo_updt_sel_victim),
        .dir_amo_hit_way_i             (uc_dir_amo_hit_way),

        .data_amo_write_o              (uc_data_amo_write),
        .data_amo_write_enable_o       (uc_data_amo_write_enable),
        .data_amo_write_set_o          (uc_data_amo_write_set),
        .data_amo_write_size_o         (uc_data_amo_write_size),
        .data_amo_write_word_o         (uc_data_amo_write_word),
        .data_amo_write_data_o         (uc_data_amo_write_data),
        .data_amo_write_be_o           (uc_data_amo_write_be),

        .lrsc_snoop_i                  (uc_lrsc_snoop),
        .lrsc_snoop_addr_i             (uc_lrsc_snoop_addr),
        .lrsc_snoop_size_i             (uc_lrsc_snoop_size),

        .core_rsp_ready_i              (uc_core_rsp_ready),
        .core_rsp_valid_o              (uc_core_rsp_valid),
        .core_rsp_o                    (uc_core_rsp),

        .mem_read_id_i                 (HPDCACHE_UC_READ_ID),
        .mem_write_id_i                (HPDCACHE_UC_WRITE_ID),

        .mem_req_read_ready_i          (mem_req_read_uc_ready),
        .mem_req_read_valid_o          (mem_req_read_uc_valid),
        .mem_req_read_o                (mem_req_read_uc),

        .mem_resp_read_ready_o         (mem_resp_read_uc_ready),
        .mem_resp_read_valid_i         (mem_resp_read_uc_valid),
        .mem_resp_read_i               (mem_resp_read_uc),

        .mem_req_write_ready_i         (mem_req_write_uc_ready),
        .mem_req_write_valid_o         (mem_req_write_uc_valid),
        .mem_req_write_o               (mem_req_write_uc),

        .mem_req_write_data_ready_i    (mem_req_write_uc_data_ready),
        .mem_req_write_data_valid_o    (mem_req_write_uc_data_valid),
        .mem_req_write_data_o          (mem_req_write_uc_data),

        .mem_resp_write_ready_o        (mem_resp_write_uc_ready),
        .mem_resp_write_valid_i        (mem_resp_write_uc_valid),
        .mem_resp_write_i              (mem_resp_write_uc),

        .cfg_error_on_cacheable_amo_i
    );
    //  }}}

    //  CMO Request Handler
    //  {{{
    hpdcache_cmo #(
        .HPDcacheCfg                   (HPDcacheCfg),

        .hpdcache_nline_t              (hpdcache_nline_t),
        .hpdcache_tag_t                (hpdcache_tag_t),
        .hpdcache_set_t                (hpdcache_set_t),
        .hpdcache_data_word_t          (hpdcache_data_word_t),
        .hpdcache_way_vector_t         (hpdcache_way_vector_t),

        .hpdcache_rsp_t                (hpdcache_rsp_t),
        .hpdcache_req_addr_t           (hpdcache_req_addr_t),
        .hpdcache_req_tid_t            (hpdcache_req_tid_t),
        .hpdcache_req_sid_t            (hpdcache_req_sid_t),
        .hpdcache_req_data_t           (hpdcache_req_data_t)
    ) hpdcache_cmo_i(
        .clk_i,
        .rst_ni,

        .wbuf_empty_i                  (wbuf_empty_o),
        .mshr_empty_i                  (miss_mshr_empty),
        .rtab_empty_i                  (rtab_empty),
        .ctrl_empty_i                  (ctrl_empty),

        .req_valid_i                   (cmo_req_valid),
        .req_ready_o                   (cmo_ready),
        .req_op_i                      (cmo_req_op),
        .req_addr_i                    (cmo_req_addr),
        .req_wdata_i                   (cmo_req_wdata),
        .req_sid_i                     (cmo_req_sid),
        .req_tid_i                     (cmo_req_tid),
        .req_need_rsp_i                (cmo_req_need_rsp),
        .req_wait_o                    (cmo_wait),

        .core_rsp_ready_i              (cmo_core_rsp_ready),
        .core_rsp_valid_o              (cmo_core_rsp_valid),
        .core_rsp_o                    (cmo_core_rsp),

        .wbuf_flush_all_o              (cmo_wbuf_flush_all),

        .dir_check_nline_o             (cmo_dir_check_nline),
        .dir_check_nline_set_o         (cmo_dir_check_nline_set),
        .dir_check_nline_tag_o         (cmo_dir_check_nline_tag),
        .dir_check_nline_hit_way_i     (cmo_dir_check_nline_hit_way),
        .dir_check_nline_wback_i       (cmo_dir_check_nline_wback),
        .dir_check_nline_dirty_i       (cmo_dir_check_nline_dirty),

        .dir_check_entry_o             (cmo_dir_check_entry),
        .dir_check_entry_set_o         (cmo_dir_check_entry_set),
        .dir_check_entry_way_o         (cmo_dir_check_entry_way),
        .dir_check_entry_valid_i       (cmo_dir_check_entry_valid),
        .dir_check_entry_wback_i       (cmo_dir_check_entry_wback),
        .dir_check_entry_dirty_i       (cmo_dir_check_entry_dirty),
        .dir_check_entry_tag_i         (cmo_dir_check_entry_tag),

        .dir_updt_o                    (cmo_dir_updt),
        .dir_updt_set_o                (cmo_dir_updt_set),
        .dir_updt_way_o                (cmo_dir_updt_way),
        .dir_updt_valid_o              (cmo_dir_updt_valid),
        .dir_updt_wback_o              (cmo_dir_updt_wback),
        .dir_updt_dirty_o              (cmo_dir_updt_dirty),
        .dir_updt_fetch_o              (cmo_dir_updt_fetch),
        .dir_updt_tag_o                (cmo_dir_updt_tag),

        .flush_empty_i                 (flush_empty),
        .flush_alloc_o                 (cmo_flush_alloc),
        .flush_alloc_ready_i           (flush_alloc_ready),
        .flush_alloc_nline_o           (cmo_flush_alloc_nline),
        .flush_alloc_way_o             (cmo_flush_alloc_way)
    );
    //  }}}

    //  Flush controller
    //  {{{
    if (HPDcacheCfg.u.wbEn) begin : gen_flush
        assign flush_alloc = ctrl_flush_alloc | cmo_flush_alloc;
        assign flush_alloc_nline =
            ctrl_flush_alloc ? ctrl_flush_alloc_nline : cmo_flush_alloc_nline;
        assign flush_alloc_way =
            ctrl_flush_alloc ? ctrl_flush_alloc_way : cmo_flush_alloc_way;

        hpdcache_flush #(
            .HPDcacheCfg                   (HPDcacheCfg),

            .hpdcache_nline_t              (hpdcache_nline_t),
            .hpdcache_set_t                (hpdcache_set_t),
            .hpdcache_word_t               (hpdcache_word_t),
            .hpdcache_way_vector_t         (hpdcache_way_vector_t),
            .hpdcache_access_data_t        (hpdcache_access_data_t),

            .hpdcache_mem_id_t             (hpdcache_mem_id_t),
            .hpdcache_mem_data_t           (hpdcache_mem_data_t),
            .hpdcache_mem_req_t            (hpdcache_mem_req_t),
            .hpdcache_mem_req_w_t          (hpdcache_mem_req_w_t),
            .hpdcache_mem_resp_w_t         (hpdcache_mem_resp_w_t)
        ) flush_i(
            .clk_i,
            .rst_ni,

            .flush_empty_o                 (flush_empty),
            .flush_full_o                  (/* open */),
            .flush_busy_o                  (flush_busy),

            .flush_check_nline_i           (flush_check_nline),
            .flush_check_hit_o             (flush_check_hit),

            .flush_alloc_i                 (flush_alloc),
            .flush_alloc_ready_o           (flush_alloc_ready),
            .flush_alloc_nline_i           (flush_alloc_nline),
            .flush_alloc_way_i             (flush_alloc_way),

            .flush_data_read_o             (flush_data_read),
            .flush_data_read_set_o         (flush_data_read_set),
            .flush_data_read_word_o        (flush_data_read_word),
            .flush_data_read_way_o         (flush_data_read_way),
            .flush_data_read_data_i        (flush_data_read_data),

            .flush_ack_o                   (flush_ack),
            .flush_ack_nline_o             (flush_ack_nline),

            .mem_req_write_ready_i         (mem_req_write_flush_ready),
            .mem_req_write_valid_o         (mem_req_write_flush_valid),
            .mem_req_write_o               (mem_req_write_flush),

            .mem_req_write_data_ready_i    (mem_req_write_flush_data_ready),
            .mem_req_write_data_valid_o    (mem_req_write_flush_data_valid),
            .mem_req_write_data_o          (mem_req_write_flush_data),

            .mem_resp_write_ready_o        (mem_resp_write_flush_ready),
            .mem_resp_write_valid_i        (mem_resp_write_flush_valid),
            .mem_resp_write_i              (mem_resp_write_flush)
        );
    end else begin : gen_no_flush
        //  The flush controller behaves as a black-hole: consumes but do not produce data
        assign flush_empty                     = 1'b1;
        assign flush_busy                      = 1'b0;
        assign flush_check_hit                 = 1'b0;
        assign flush_alloc_ready               = 1'b1;
        assign flush_data_read                 = 1'b0;
        assign flush_data_read_set             = '0;
        assign flush_data_read_word            = '0;
        assign flush_data_read_way             = '0;
        assign flush_ack                       = 1'b0;
        assign flush_ack_nline                 = '0;
        assign mem_req_write_flush_valid       = 1'b0;
        assign mem_req_write_flush             = '{
            mem_req_command: HPDCACHE_MEM_READ,
            mem_req_atomic : HPDCACHE_MEM_ATOMIC_ADD,
            default        : '0
        };
        assign mem_req_write_flush_data_valid  = 1'b0;
        assign mem_req_write_flush_data        = '0;
        assign mem_resp_write_flush_ready      = 1'b1;
    end
    //  }}}

    //  Read and Write Arbiters for Memory interfaces
    //  {{{

    //      Read request interface
    //
    //      There is a fixed-priority arbiter between:
    //      - the miss_handler (higher priority);
    //      - the uncacheable request handler (lower priority)
    logic              [1:0] arb_mem_req_read_ready;
    logic              [1:0] arb_mem_req_read_valid;
    hpdcache_mem_req_t [1:0] arb_mem_req_read;

    assign mem_req_read_miss_ready = arb_mem_req_read_ready[0];
    assign arb_mem_req_read_valid[0] = mem_req_read_miss_valid;
    assign arb_mem_req_read[0] = mem_req_read_miss;

    assign mem_req_read_uc_ready = arb_mem_req_read_ready[1];
    assign arb_mem_req_read_valid[1] = mem_req_read_uc_valid;
    assign arb_mem_req_read[1] = mem_req_read_uc;

    hpdcache_mem_req_read_arbiter #(
        .N                     (2),
        .hpdcache_mem_req_t    (hpdcache_mem_req_t)
    ) hpdcache_mem_req_read_arbiter_i(
        .clk_i,
        .rst_ni,

        .mem_req_read_ready_o  (arb_mem_req_read_ready),
        .mem_req_read_valid_i  (arb_mem_req_read_valid),
        .mem_req_read_i        (arb_mem_req_read),

        .mem_req_read_ready_i,
        .mem_req_read_valid_o,
        .mem_req_read_o        (mem_req_read_o)
    );

    //      Read response interface
    always_comb
    begin : mem_resp_read_demux_comb
        mem_resp_read_uc_valid = 1'b0;
        mem_resp_read_miss_valid = 1'b0;
        mem_resp_read_ready_o = 1'b0;
        if (mem_resp_read_valid_i) begin
            if (mem_resp_read_i.mem_resp_r_id == {HPDcacheCfg.u.memIdWidth{1'b1}}) begin
                mem_resp_read_uc_valid = 1'b1;
                mem_resp_read_ready_o = mem_resp_read_uc_ready;
            end else begin
                mem_resp_read_miss_valid = 1'b1;
                mem_resp_read_ready_o = mem_resp_read_miss_ready;
            end
        end
    end

    assign mem_resp_read_uc               = mem_resp_read_i;
    assign mem_resp_read_miss             = mem_resp_read_i;
`ifdef HPDCACHE_OPENPITON
    assign mem_resp_read_miss_inval       = mem_resp_read_inval_i;
    assign mem_resp_read_miss_inval_nline = mem_resp_read_inval_nline_i;
`else
    assign mem_resp_read_miss_inval       = 1'b0;
    assign mem_resp_read_miss_inval_nline = '0;
`endif

    //      Write request interface
    //
    //      There is a fixed-priority arbiter between:
    //      - the flush controller (higher priority)
    //      - the write buffer
    //      - the uncacheable request handler (lower priority)
    logic                [2:0] arb_mem_req_write_ready;
    logic                [2:0] arb_mem_req_write_valid;
    hpdcache_mem_req_t   [2:0] arb_mem_req_write;

    logic                [2:0] arb_mem_req_write_data_valid;
    logic                [2:0] arb_mem_req_write_data_ready;
    hpdcache_mem_req_w_t [2:0] arb_mem_req_write_data;

    //      Split the ID space into 3 segments:
    //      1111...1111  -> Uncached writes
    //      1xxx...xxxx  -> Flush writes (where at least one x is 0)
    //      0xxx...xxxx  -> Write buffer writes
    function automatic hpdcache_mem_req_t hpdcache_req_write_sel_id(
        hpdcache_mem_req_t req, int kind
    );
        //  Request from the write buffer
        unique if (kind == 0) begin
            req.mem_req_id = {1'b0, req.mem_req_id[0 +: HPDcacheCfg.u.memIdWidth-1]};
        end
        //  Request from the flush controller
        else if (kind == 1) begin
            req.mem_req_id = {1'b1, req.mem_req_id[0 +: HPDcacheCfg.u.memIdWidth-1]};
        end
        //  Request from the uncached controller
        else if (kind == 2) begin
            req.mem_req_id = '1;
        end
        return req;
    endfunction

    function automatic hpdcache_mem_resp_w_t hpdcache_resp_write_sel_id(
        hpdcache_mem_resp_w_t resp, int kind
    );
        //  Response to the write buffer
        unique if (kind == 0) begin
            resp.mem_resp_w_id = {1'b0, resp.mem_resp_w_id[0 +: HPDcacheCfg.u.memIdWidth-1]};
        end
        //  Response to the flush controller
        else if (kind == 1) begin
            resp.mem_resp_w_id = {1'b0, resp.mem_resp_w_id[0 +: HPDcacheCfg.u.memIdWidth-1]};
        end
        //  Response to the uncached controller
        else if (kind == 2) begin
            resp.mem_resp_w_id = '1;
        end
        return resp;
    endfunction

    assign mem_req_write_wbuf_ready        = arb_mem_req_write_ready[0];
    assign arb_mem_req_write_valid[0]      = mem_req_write_wbuf_valid;
    assign arb_mem_req_write[0]            = hpdcache_req_write_sel_id(mem_req_write_wbuf, 0);

    assign mem_req_write_wbuf_data_ready   = arb_mem_req_write_data_ready[0];
    assign arb_mem_req_write_data_valid[0] = mem_req_write_wbuf_data_valid;
    assign arb_mem_req_write_data[0]       = mem_req_write_wbuf_data;

    assign mem_req_write_flush_ready       = arb_mem_req_write_ready[1];
    assign arb_mem_req_write_valid[1]      = mem_req_write_flush_valid;
    assign arb_mem_req_write[1]            = hpdcache_req_write_sel_id(mem_req_write_flush, 1);

    assign mem_req_write_flush_data_ready  = arb_mem_req_write_data_ready[1];
    assign arb_mem_req_write_data_valid[1] = mem_req_write_flush_data_valid;
    assign arb_mem_req_write_data[1]       = mem_req_write_flush_data;

    assign mem_req_write_uc_ready          = arb_mem_req_write_ready[2];
    assign arb_mem_req_write_valid[2]      = mem_req_write_uc_valid;
    assign arb_mem_req_write[2]            = hpdcache_req_write_sel_id(mem_req_write_uc, 2);

    assign mem_req_write_uc_data_ready     = arb_mem_req_write_data_ready[2];
    assign arb_mem_req_write_data_valid[2] = mem_req_write_uc_data_valid;
    assign arb_mem_req_write_data[2]       = mem_req_write_uc_data;

    hpdcache_mem_req_write_arbiter #(
        .N                             (3),
        .hpdcache_mem_req_t            (hpdcache_mem_req_t),
        .hpdcache_mem_req_w_t          (hpdcache_mem_req_w_t)
    ) hpdcache_mem_req_write_arbiter_i (
        .clk_i,
        .rst_ni,

        .mem_req_write_ready_o         (arb_mem_req_write_ready),
        .mem_req_write_valid_i         (arb_mem_req_write_valid),
        .mem_req_write_i               (arb_mem_req_write),

        .mem_req_write_data_ready_o    (arb_mem_req_write_data_ready),
        .mem_req_write_data_valid_i    (arb_mem_req_write_data_valid),
        .mem_req_write_data_i          (arb_mem_req_write_data),

        .mem_req_write_ready_i,
        .mem_req_write_valid_o,
        .mem_req_write_o               (mem_req_write_o),

        .mem_req_write_data_ready_i,
        .mem_req_write_data_valid_o,
        .mem_req_write_data_o          (mem_req_write_data_o)
    );

    //      Write response interface
    always_comb
    begin : mem_resp_write_demux_comb
        mem_resp_write_flush_valid = 1'b0;
        mem_resp_write_wbuf_valid = 1'b0;
        mem_resp_write_uc_valid = 1'b0;
        mem_resp_write_ready_o = 1'b0;
        if (mem_resp_write_valid_i) begin
            if (mem_resp_write_i.mem_resp_w_id == {HPDcacheCfg.u.memIdWidth{1'b1}}) begin
                mem_resp_write_uc_valid = 1'b1;
                mem_resp_write_ready_o = mem_resp_write_uc_ready;
            end else if (mem_resp_write_i.mem_resp_w_id[HPDcacheCfg.u.memIdWidth-1]) begin
                mem_resp_write_flush_valid = 1'b1;
                mem_resp_write_ready_o = mem_resp_write_flush_ready;
            end else begin
                mem_resp_write_wbuf_valid = 1'b1;
                mem_resp_write_ready_o = mem_resp_write_wbuf_ready;
            end
        end
    end

    assign mem_resp_write_wbuf = hpdcache_resp_write_sel_id(mem_resp_write_i, 0);
    assign mem_resp_write_flush = hpdcache_resp_write_sel_id(mem_resp_write_i, 1);
    assign mem_resp_write_uc = hpdcache_resp_write_sel_id(mem_resp_write_i, 2);
    //  }}}

    //  Assertions
    //  {{{
`ifndef HPDCACHE_ASSERT_OFF
    assert property (@(posedge clk_i) disable iff (!rst_ni)
        ctrl_flush_alloc |-> !cmo_flush_alloc) else
            $error("Unsupported concurrent flush from ctrl and cmo");

    initial begin
        word_width_assert:
            assert (HPDcacheCfg.u.wordWidth inside {32, 64}) else
                $fatal("word width shall be 32 or 64");
        req_access_width_assert:
            assert (HPDcacheCfg.u.reqWords <= HPDcacheCfg.u.accessWords) else
                $fatal("req data width shall be l.e. to cache access width");
        refill_access_width_assert:
            assert (HPDcacheCfg.u.clWords >= HPDcacheCfg.u.accessWords) else
                $fatal("cache access width shall be l.e. to cache-line width");
        cl_words_assert:
            assert (HPDcacheCfg.u.clWords > 1) else
                $fatal("cacheline words shall be greater than 1");
        mem_width_assert:
            assert (HPDcacheCfg.u.memDataWidth >= HPDcacheCfg.reqDataWidth) else
                $fatal("memory interface data width shall be g.e. to req data width");
        miss_mem_id_width_assert:
            assert (HPDcacheCfg.u.memIdWidth >=
                ($clog2(HPDcacheCfg.u.mshrWays * HPDcacheCfg.u.mshrSets) + 1)) else
                $fatal("insufficient ID bits on the mem interface to transport misses");
        wbuf_mem_id_width_assert:
            assert (HPDcacheCfg.u.memIdWidth >= (HPDcacheCfg.wbufDirPtrWidth + 1)) else
                $fatal("insufficient ID bits on the mem interface to transport writes");
        wt_or_wb_assert:
            assert (HPDcacheCfg.u.wtEn || HPDcacheCfg.u.wbEn) else
                $fatal("the cache shall be configured to support WT, WB or both");
    end
`endif
    // }}}

endmodule
