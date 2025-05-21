/**
 *  Copyright 2023,2024 CEA*
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
/**
 *  Author(s)  : Cesar Fuguet
 *  Date       : October, 2024
 *  Description: HPDcache testbench wrapper
 */
`include "hpdcache_typedef.svh"

module hpdcache_wrapper
import hpdcache_pkg::*;
    //  Parameters
    //  {{{
#(
    localparam hpdcache_user_cfg_t UserCfg = '{
        nRequesters: (4'b1 << `CONF_HPDCACHE_REQ_SRC_ID_WIDTH),
        paWidth: `CONF_HPDCACHE_PA_WIDTH,
        wordWidth: `CONF_HPDCACHE_WORD_WIDTH,
        sets: `CONF_HPDCACHE_SETS,
        ways: `CONF_HPDCACHE_WAYS,
        clWords: `CONF_HPDCACHE_CL_WORDS,
        reqWords: `CONF_HPDCACHE_REQ_WORDS,
        reqTransIdWidth: `CONF_HPDCACHE_REQ_TRANS_ID_WIDTH,
        reqSrcIdWidth: `CONF_HPDCACHE_REQ_SRC_ID_WIDTH,
        victimSel: `CONF_HPDCACHE_VICTIM_SEL,
        dataWaysPerRamWord: `CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD,
        dataSetsPerRam: `CONF_HPDCACHE_DATA_SETS_PER_RAM,
        dataRamByteEnable: `CONF_HPDCACHE_DATA_RAM_WBYTEENABLE,
        accessWords: `CONF_HPDCACHE_ACCESS_WORDS,
        mshrSets: `CONF_HPDCACHE_MSHR_SETS,
        mshrWays: `CONF_HPDCACHE_MSHR_WAYS,
        mshrWaysPerRamWord: `CONF_HPDCACHE_MSHR_WAYS_PER_RAM_WORD,
        mshrSetsPerRam: `CONF_HPDCACHE_MSHR_SETS_PER_RAM,
        mshrRamByteEnable: `CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE,
        mshrUseRegbank: `CONF_HPDCACHE_MSHR_USE_REGBANK,
        refillCoreRspFeedthrough: `CONF_HPDCACHE_REFILL_CORE_RSP_FEEDTHROUGH,
        refillFifoDepth: `CONF_HPDCACHE_REFILL_FIFO_DEPTH,
        wbufDirEntries: `CONF_HPDCACHE_WBUF_DIR_ENTRIES,
        wbufDataEntries: `CONF_HPDCACHE_WBUF_DATA_ENTRIES,
        wbufWords: `CONF_HPDCACHE_WBUF_WORDS,
        wbufTimecntWidth: `CONF_HPDCACHE_WBUF_TIMECNT_WIDTH,
        rtabEntries: `CONF_HPDCACHE_RTAB_ENTRIES,
        flushEntries: `CONF_HPDCACHE_FLUSH_ENTRIES,
        flushFifoDepth: `CONF_HPDCACHE_FLUSH_FIFO_DEPTH,
        memAddrWidth: `CONF_HPDCACHE_MEM_ADDR_WIDTH,
        memIdWidth: `CONF_HPDCACHE_MEM_ID_WIDTH,
        memDataWidth: `CONF_HPDCACHE_MEM_DATA_WIDTH,
        wtEn: `CONF_HPDCACHE_WT_ENABLE,
        wbEn: `CONF_HPDCACHE_WB_ENABLE
    },

    localparam hpdcache_cfg_t Cfg = hpdcacheBuildConfig(UserCfg),
    localparam type wbuf_timecnt_t = logic unsigned [Cfg.u.wbufTimecntWidth-1:0],

    //      Request Interface Definitions
    //      {{{
    localparam type hpdcache_tag_t = logic [Cfg.tagWidth-1:0],
    localparam type hpdcache_data_word_t = logic [Cfg.u.wordWidth-1:0],
    localparam type hpdcache_data_be_t = logic [Cfg.u.wordWidth/8-1:0],
    localparam type hpdcache_req_offset_t = logic [Cfg.reqOffsetWidth-1:0],
    localparam type hpdcache_req_data_t = hpdcache_data_word_t [Cfg.u.reqWords-1:0],
    localparam type hpdcache_req_be_t = hpdcache_data_be_t [Cfg.u.reqWords-1:0],
    localparam type hpdcache_req_sid_t = logic [Cfg.u.reqSrcIdWidth-1:0],
    localparam type hpdcache_req_tid_t = logic [Cfg.u.reqTransIdWidth-1:0],
    localparam type hpdcache_req_t =
            `HPDCACHE_DECL_REQ_T(
                    hpdcache_req_offset_t,
                    hpdcache_req_data_t,
                    hpdcache_req_be_t,
                    hpdcache_req_sid_t,
                    hpdcache_req_tid_t,
                    hpdcache_tag_t),
    localparam type hpdcache_rsp_t =
            `HPDCACHE_DECL_RSP_T(
                    hpdcache_req_data_t,
                    hpdcache_req_sid_t,
                    hpdcache_req_tid_t),
    //      }}}

    localparam type hpdcache_mem_addr_t = logic [Cfg.u.memAddrWidth-1:0],
    localparam type hpdcache_mem_id_t   = logic [Cfg.u.memIdWidth-1:0],
    localparam type hpdcache_mem_data_t = logic [Cfg.u.memDataWidth-1:0],
    localparam type hpdcache_mem_be_t   = logic [Cfg.u.memDataWidth/8-1:0]
)
    //  }}}

    //  Ports
    //  {{{
(
    //      Clock and reset signals
    input  wire logic                          clk_i,
    input  wire logic                          rst_ni,

    //      Force the write buffer to send all pending writes
    input  wire logic                          wbuf_flush_i,

    //      Core request interface
    //         1st cycle
    input  logic                               core_req_valid_i,
    output logic                               core_req_ready_o,
    input  hpdcache_req_t                      core_req_i,
    //         2nd cycle
    input  logic                               core_req_abort_i,
    input  hpdcache_tag_t                      core_req_tag_i,
    input  hpdcache_pma_t                      core_req_pma_i,

    //      Core response interface
    output var  logic                          core_rsp_valid_o,
    output var  hpdcache_rsp_t                 core_rsp_o,

    //      Memory read interface
    input  wire logic                          mem_req_read_ready_i,
    output wire logic                          mem_req_read_valid_o,
    output wire hpdcache_mem_addr_t            mem_req_read_addr_o,
    output wire hpdcache_mem_len_t             mem_req_read_len_o,
    output wire hpdcache_mem_size_t            mem_req_read_size_o,
    output wire hpdcache_mem_id_t              mem_req_read_id_o,
    output wire hpdcache_mem_command_e         mem_req_read_command_o,
    output wire hpdcache_mem_atomic_e          mem_req_read_atomic_o,
    output wire logic                          mem_req_read_cacheable_o,

    output var  logic                          mem_resp_read_ready_o,
    input  wire logic                          mem_resp_read_valid_i,
    input  wire hpdcache_mem_error_e           mem_resp_read_error_i,
    input  wire hpdcache_mem_id_t              mem_resp_read_id_i,
    input  wire hpdcache_mem_data_t            mem_resp_read_data_i,
    input  wire logic                          mem_resp_read_last_i,

    //      Memory write interface
    input  wire logic                          mem_req_write_ready_i,
    output wire logic                          mem_req_write_valid_o,
    output wire hpdcache_mem_addr_t            mem_req_write_addr_o,
    output wire hpdcache_mem_len_t             mem_req_write_len_o,
    output wire hpdcache_mem_size_t            mem_req_write_size_o,
    output wire hpdcache_mem_id_t              mem_req_write_id_o,
    output wire hpdcache_mem_command_e         mem_req_write_command_o,
    output wire hpdcache_mem_atomic_e          mem_req_write_atomic_o,
    output wire logic                          mem_req_write_cacheable_o,

    input  wire logic                          mem_req_write_data_ready_i,
    output wire logic                          mem_req_write_data_valid_o,
    output wire hpdcache_mem_data_t            mem_req_write_data_o,
    output wire hpdcache_mem_be_t              mem_req_write_be_o,
    output wire logic                          mem_req_write_last_o,

    output var  logic                          mem_resp_write_ready_o,
    input  wire logic                          mem_resp_write_valid_i,
    input  wire logic                          mem_resp_write_is_atomic_i,
    input  wire hpdcache_mem_error_e           mem_resp_write_error_i,
    input  wire hpdcache_mem_id_t              mem_resp_write_id_i,

    //      Performance events
    output wire  logic                         evt_cache_write_miss_o,
    output wire  logic                         evt_cache_read_miss_o,
    output wire  logic                         evt_uncached_req_o,
    output wire  logic                         evt_cmo_req_o,
    output wire  logic                         evt_write_req_o,
    output wire  logic                         evt_read_req_o,
    output wire  logic                         evt_prefetch_req_o,
    output wire  logic                         evt_req_on_hold_o,
    output wire  logic                         evt_rtab_rollback_o,
    output wire  logic                         evt_stall_refill_o,
    output wire  logic                         evt_stall_o,

    //      Status interface
    output wire  logic                         wbuf_empty_o,

    //      Configuration interface
    input  wire logic                          cfg_enable_i,
    input  wire wbuf_timecnt_t                 cfg_wbuf_threshold_i,
    input  wire logic                          cfg_wbuf_reset_timecnt_on_write_i,
    input  wire logic                          cfg_wbuf_sequential_waw_i,
    input  wire logic                          cfg_wbuf_inhibit_write_coalescing_i,
    input  wire logic                          cfg_prefetch_updt_plru_i,
    input  wire logic                          cfg_error_on_cacheable_amo_i,
    input  wire logic                          cfg_rtab_single_entry_i,
    input  wire logic                          cfg_default_wb_i
);
    //  }}}

    //  Declaration of internal types
    //  {{{
    `HPDCACHE_TYPEDEF_MEM_REQ_T(hpdcache_mem_req_t, hpdcache_mem_addr_t, hpdcache_mem_id_t);
    `HPDCACHE_TYPEDEF_MEM_RESP_R_T(hpdcache_mem_resp_r_t, hpdcache_mem_id_t, hpdcache_mem_data_t);
    `HPDCACHE_TYPEDEF_MEM_REQ_W_T(hpdcache_mem_req_w_t, hpdcache_mem_data_t, hpdcache_mem_be_t);
    `HPDCACHE_TYPEDEF_MEM_RESP_W_T(hpdcache_mem_resp_w_t, hpdcache_mem_id_t);
    //  }}}

    //  Declaration of internal signals
    //  {{{
    localparam int unsigned NREQUESTERS = Cfg.u.nRequesters;

    logic                  core_req_valid [NREQUESTERS];
    logic                  core_req_ready [NREQUESTERS];
    hpdcache_req_t         core_req       [NREQUESTERS];
    logic                  core_req_abort [NREQUESTERS];
    hpdcache_tag_t         core_req_tag   [NREQUESTERS];
    hpdcache_pma_t         core_req_pma   [NREQUESTERS];

    //      Core response interface
    logic                  core_rsp_valid [NREQUESTERS];
    hpdcache_rsp_t         core_rsp       [NREQUESTERS];

    hpdcache_mem_req_t     mem_req_read;
    hpdcache_mem_resp_r_t  mem_resp_read;
    hpdcache_mem_req_t     mem_req_write;
    hpdcache_mem_req_w_t   mem_req_write_data;
    hpdcache_mem_resp_w_t  mem_resp_write;
    //  }}}

    //  Write/read to/from memory interfaces
    //  {{{
    assign mem_req_read_addr_o      = mem_req_read.mem_req_addr,
           mem_req_read_len_o       = mem_req_read.mem_req_len,
           mem_req_read_size_o      = mem_req_read.mem_req_size,
           mem_req_read_id_o        = mem_req_read.mem_req_id,
           mem_req_read_command_o   = mem_req_read.mem_req_command,
           mem_req_read_atomic_o    = mem_req_read.mem_req_atomic,
           mem_req_read_cacheable_o = mem_req_read.mem_req_cacheable;

    assign mem_resp_read.mem_resp_r_error = mem_resp_read_error_i,
           mem_resp_read.mem_resp_r_id    = mem_resp_read_id_i,
           mem_resp_read.mem_resp_r_data  = mem_resp_read_data_i,
           mem_resp_read.mem_resp_r_last  = mem_resp_read_last_i;

    assign mem_req_write_addr_o      = mem_req_write.mem_req_addr,
           mem_req_write_len_o       = mem_req_write.mem_req_len,
           mem_req_write_size_o      = mem_req_write.mem_req_size,
           mem_req_write_id_o        = mem_req_write.mem_req_id,
           mem_req_write_command_o   = mem_req_write.mem_req_command,
           mem_req_write_atomic_o    = mem_req_write.mem_req_atomic,
           mem_req_write_cacheable_o = mem_req_write.mem_req_cacheable;

    assign mem_req_write_data_o      = mem_req_write_data.mem_req_w_data,
           mem_req_write_be_o        = mem_req_write_data.mem_req_w_be,
           mem_req_write_last_o      = mem_req_write_data.mem_req_w_last;

    assign mem_resp_write.mem_resp_w_is_atomic = mem_resp_write_is_atomic_i,
           mem_resp_write.mem_resp_w_error     = mem_resp_write_error_i,
           mem_resp_write.mem_resp_w_id        = mem_resp_write_id_i;
    //  }}}

    always_comb
    begin : core_req_routing_comb
        core_req_ready_o = core_req_valid_i && core_req_ready[core_req_i.sid];
        for (int i = 0; i < NREQUESTERS; i++) begin
            core_req_valid [i] = core_req_valid_i && (core_req_i.sid == hpdcache_req_sid_t'(i));
            core_req       [i] = core_req_i;
            core_req_abort [i] = core_req_abort_i;
            core_req_tag   [i] = core_req_tag_i;
            core_req_pma   [i] = core_req_pma_i;
        end
    end

    always_comb
    begin : core_rsp_routing_comb
        core_rsp_valid_o = '0;
        core_rsp_o       = '0;
        for (int i = 0; i < NREQUESTERS; i++) begin
            if (core_rsp_valid[i]) begin
                core_rsp_valid_o = 1'b1;
                core_rsp_o       = core_rsp[i];
                break;
            end
        end
    end

    hpdcache #(
        .HPDcacheCfg                       (Cfg),
        .wbuf_timecnt_t                    (wbuf_timecnt_t),
        .hpdcache_tag_t                    (hpdcache_tag_t),
        .hpdcache_data_word_t              (hpdcache_data_word_t),
        .hpdcache_data_be_t                (hpdcache_data_be_t),
        .hpdcache_req_offset_t             (hpdcache_req_offset_t),
        .hpdcache_req_data_t               (hpdcache_req_data_t),
        .hpdcache_req_be_t                 (hpdcache_req_be_t),
        .hpdcache_req_sid_t                (hpdcache_req_sid_t),
        .hpdcache_req_tid_t                (hpdcache_req_tid_t),
        .hpdcache_req_t                    (hpdcache_req_t),
        .hpdcache_rsp_t                    (hpdcache_rsp_t),
        .hpdcache_mem_addr_t               (hpdcache_mem_addr_t),
        .hpdcache_mem_id_t                 (hpdcache_mem_id_t),
        .hpdcache_mem_data_t               (hpdcache_mem_data_t),
        .hpdcache_mem_be_t                 (hpdcache_mem_be_t),
        .hpdcache_mem_req_t                (hpdcache_mem_req_t),
        .hpdcache_mem_req_w_t              (hpdcache_mem_req_w_t),
        .hpdcache_mem_resp_r_t             (hpdcache_mem_resp_r_t),
        .hpdcache_mem_resp_w_t             (hpdcache_mem_resp_w_t)
    ) i_hpdcache(
        .clk_i,
        .rst_ni,

        .wbuf_flush_i,

        .core_req_valid_i                  (core_req_valid),
        .core_req_ready_o                  (core_req_ready),
        .core_req_i                        (core_req),
        .core_req_abort_i                  (core_req_abort),
        .core_req_tag_i                    (core_req_tag),
        .core_req_pma_i                    (core_req_pma),

        .core_rsp_valid_o                  (core_rsp_valid),
        .core_rsp_o                        (core_rsp),

        .mem_req_read_ready_i              (mem_req_read_ready_i),
        .mem_req_read_valid_o              (mem_req_read_valid_o),
        .mem_req_read_o                    (mem_req_read),

        .mem_resp_read_ready_o             (mem_resp_read_ready_o),
        .mem_resp_read_valid_i             (mem_resp_read_valid_i),
        .mem_resp_read_i                   (mem_resp_read),

        .mem_req_write_ready_i             (mem_req_write_ready_i),
        .mem_req_write_valid_o             (mem_req_write_valid_o),
        .mem_req_write_o                   (mem_req_write),

        .mem_req_write_data_ready_i        (mem_req_write_data_ready_i),
        .mem_req_write_data_valid_o        (mem_req_write_data_valid_o),
        .mem_req_write_data_o              (mem_req_write_data),

        .mem_resp_write_ready_o            (mem_resp_write_ready_o),
        .mem_resp_write_valid_i            (mem_resp_write_valid_i),
        .mem_resp_write_i                  (mem_resp_write),

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
        .evt_stall_o,

        .wbuf_empty_o,

        .cfg_enable_i,
        .cfg_wbuf_threshold_i,
        .cfg_wbuf_reset_timecnt_on_write_i,
        .cfg_wbuf_sequential_waw_i,
        .cfg_wbuf_inhibit_write_coalescing_i,
        .cfg_prefetch_updt_plru_i,
        .cfg_error_on_cacheable_amo_i,
        .cfg_rtab_single_entry_i,
        .cfg_default_wb_i
    );

    //  Assertions/Coverage
    //  {{{
    //  pragma translate_off
    wbuf_not_ready_cover: cover property (
        @(posedge clk_i) i_hpdcache.hpdcache_ctrl_i.wbuf_write_o &
                        ~i_hpdcache.hpdcache_ctrl_i.wbuf_write_ready_i);
    //  pragma translate_on
    //  }}}

endmodule
