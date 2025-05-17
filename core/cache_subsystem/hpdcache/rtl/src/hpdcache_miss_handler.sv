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
 *  Description   : HPDcache Miss Handler
 *  History       :
 */
module hpdcache_miss_handler
//  {{{
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    parameter type hpdcache_nline_t = logic,
    parameter type hpdcache_set_t = logic,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_word_t = logic,

    parameter type hpdcache_way_vector_t = logic,
    parameter type hpdcache_way_t = logic,

    parameter type hpdcache_dir_entry_t = logic,

    parameter type hpdcache_refill_data_t = logic,

    parameter type hpdcache_req_data_t = logic,
    parameter type hpdcache_req_offset_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_tid_t = logic,

    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic,

    parameter type hpdcache_mem_id_t = logic,
    parameter type hpdcache_mem_req_t = logic,
    parameter type hpdcache_mem_resp_r_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,

    //      Global control signals
    //      {{{
    output logic                  mshr_empty_o,
    output logic                  mshr_full_o,
    //      }}}

    //      Configuration signals
    //      {{{
    input  logic                  cfg_prefetch_updt_sel_victim_i,
    //      }}}

    //      CHECK interface
    //      {{{
    input  logic                  mshr_check_i,
    input  hpdcache_req_offset_t  mshr_check_offset_i,
    input  hpdcache_nline_t       mshr_check_nline_i,
    output logic                  mshr_check_hit_o,
    //      }}}

    //      MISS interface
    //      {{{
    //          MISS request interface
    output logic                  mshr_alloc_ready_o,
    input  logic                  mshr_alloc_i,
    input  logic                  mshr_alloc_cs_i,
    input  hpdcache_nline_t       mshr_alloc_nline_i,
    output logic                  mshr_alloc_full_o,
    input  hpdcache_req_tid_t     mshr_alloc_tid_i,
    input  hpdcache_req_sid_t     mshr_alloc_sid_i,
    input  hpdcache_word_t        mshr_alloc_word_i,
    input  hpdcache_way_vector_t  mshr_alloc_victim_way_i,
    input  logic                  mshr_alloc_need_rsp_i,
    input  logic                  mshr_alloc_is_prefetch_i,
    input  logic                  mshr_alloc_wback_i,

    //          REFILL MISS / Invalidation interface
    input  logic                  refill_req_ready_i,
    output logic                  refill_req_valid_o,
    output logic                  refill_is_error_o,
    output logic                  refill_busy_o,
    output logic                  refill_updt_sel_victim_o,
    output hpdcache_set_t         refill_set_o,
    output hpdcache_way_vector_t  refill_way_o,
    output hpdcache_dir_entry_t   refill_dir_entry_o,
    output logic                  refill_write_dir_o,
    output logic                  refill_write_data_o,
    output hpdcache_refill_data_t refill_data_o,
    output hpdcache_word_t        refill_word_o,
    output hpdcache_nline_t       refill_nline_o,
    output logic                  refill_updt_rtab_o,

    output logic                  inval_check_dir_o,
    output logic                  inval_write_dir_o,
    output hpdcache_nline_t       inval_nline_o,
    input  logic                  inval_hit_i,

    //          REFILL core response interface
    output logic                  refill_core_rsp_valid_o,
    output hpdcache_rsp_t         refill_core_rsp_o,
    //      }}}

    //      MEMORY interface
    //      {{{
    input  logic                  mem_req_ready_i,
    output logic                  mem_req_valid_o,
    output hpdcache_mem_req_t     mem_req_o,

    output logic                  mem_resp_ready_o,
    input  logic                  mem_resp_valid_i,
    input  hpdcache_mem_resp_r_t  mem_resp_i,
    input  logic                  mem_resp_inval_i,
    input  hpdcache_nline_t       mem_resp_inval_nline_i
    //      }}}
);
//  }}}

    //  Declaration of constants and types
    //  {{{
    localparam hpdcache_uint REFILL_REQ_RATIO = HPDcacheCfg.u.accessWords /
                                                HPDcacheCfg.u.reqWords;
    localparam hpdcache_uint REFILL_LAST_CHUNK_WORD = HPDcacheCfg.u.clWords -
                                                      HPDcacheCfg.u.accessWords;

    typedef enum logic {
        MISS_REQ_IDLE = 1'b0,
        MISS_REQ_SEND = 1'b1
    } miss_req_fsm_e;

    typedef enum {
        REFILL_IDLE,
        REFILL_WRITE,
        REFILL_WRITE_DIR,
        REFILL_INVAL
    } refill_fsm_e;

    typedef struct packed {
        hpdcache_mem_error_e r_error;
        hpdcache_mem_id_t    r_id;
        logic                is_inval;
        hpdcache_nline_t     inval_nline;
    } mem_resp_metadata_t;

    typedef logic [HPDcacheCfg.mshrWayWidth-1:0] mshr_way_t;
    typedef logic [HPDcacheCfg.mshrSetWidth-1:0] mshr_set_t;
    //  }}}

    //  Declaration of internal signals and registers
    //  {{{
    miss_req_fsm_e           miss_req_fsm_q, miss_req_fsm_d;
    mshr_way_t               mshr_alloc_way_q, mshr_alloc_way_d;
    hpdcache_nline_t         mshr_alloc_nline_q;

    refill_fsm_e             refill_fsm_q, refill_fsm_d;
    hpdcache_set_t           refill_set_q;
    hpdcache_tag_t           refill_tag_q;
    hpdcache_way_t           refill_way_q;
    hpdcache_req_sid_t       refill_sid_q;
    hpdcache_req_tid_t       refill_tid_q;
    hpdcache_word_t          refill_cnt_q, refill_cnt_d;
    logic                    refill_need_rsp_q;
    logic                    refill_is_prefetch_q;
    logic                    refill_wback_q;
    hpdcache_word_t          refill_core_rsp_word_q;
    hpdcache_way_t           refill_way;

    mem_resp_metadata_t      refill_fifo_resp_meta_wdata, refill_fifo_resp_meta_rdata;
    logic                    refill_fifo_resp_meta_w, refill_fifo_resp_meta_wok;
    logic                    refill_fifo_resp_meta_r, refill_fifo_resp_meta_rok;

    logic                    refill_fifo_resp_data_w, refill_fifo_resp_data_wok;
    hpdcache_refill_data_t   refill_fifo_resp_data_rdata;
    logic                    refill_fifo_resp_data_r;

    logic                    refill_core_rsp_valid;
    hpdcache_req_data_t      refill_core_rsp_rdata;
    hpdcache_req_sid_t       refill_core_rsp_sid;
    hpdcache_req_tid_t       refill_core_rsp_tid;
    logic                    refill_core_rsp_error;
    hpdcache_word_t          refill_core_rsp_word;
    hpdcache_rsp_t           refill_core_rsp;

    hpdcache_set_t           mshr_check_set;
    hpdcache_tag_t           mshr_check_tag;
    logic                    mshr_alloc;
    logic                    mshr_alloc_cs;
    hpdcache_way_t           mshr_alloc_victim_way;
    logic                    mshr_ack;
    logic                    mshr_ack_cs;
    mshr_set_t               mshr_ack_set;
    mshr_way_t               mshr_ack_way;
    hpdcache_set_t           mshr_ack_cache_set;
    hpdcache_way_t           mshr_ack_cache_way;
    hpdcache_tag_t           mshr_ack_cache_tag;
    hpdcache_req_sid_t       mshr_ack_src_id;
    hpdcache_req_tid_t       mshr_ack_req_id;
    hpdcache_word_t          mshr_ack_word;
    logic                    mshr_ack_need_rsp;
    logic                    mshr_ack_is_prefetch;
    logic                    mshr_ack_wback;
    logic                    mshr_empty;
    //  }}}

    //  Miss Request FSM
    //  {{{
    always_comb
    begin : miss_req_fsm_comb
        mshr_alloc_ready_o = 1'b0;
        mshr_alloc         = 1'b0;
        mshr_alloc_cs      = 1'b0;
        mem_req_valid_o    = 1'b0;

        miss_req_fsm_d     = miss_req_fsm_q;

        unique case (miss_req_fsm_q)
            MISS_REQ_IDLE: begin
                mshr_alloc_ready_o = 1'b1;
                mshr_alloc         = mshr_alloc_i;
                mshr_alloc_cs      = mshr_alloc_cs_i;
                if (mshr_alloc_i) begin
                    miss_req_fsm_d = MISS_REQ_SEND;
                end else begin
                    miss_req_fsm_d = MISS_REQ_IDLE;
                end
            end
            MISS_REQ_SEND: begin
                mem_req_valid_o = 1'b1;
                if (mem_req_ready_i) begin
                    miss_req_fsm_d = MISS_REQ_IDLE;
                end else begin
                    miss_req_fsm_d = MISS_REQ_SEND;
                end
            end
        endcase
    end

    localparam hpdcache_uint REFILL_REQ_SIZE = $clog2(HPDcacheCfg.u.memDataWidth / 8);
    localparam hpdcache_uint REFILL_REQ_LEN = HPDcacheCfg.clWidth / HPDcacheCfg.u.memDataWidth;

    assign mem_req_o.mem_req_addr = {mshr_alloc_nline_q, {HPDcacheCfg.clOffsetWidth{1'b0}} };
    assign mem_req_o.mem_req_len = hpdcache_mem_len_t'(REFILL_REQ_LEN-1);
    assign mem_req_o.mem_req_size = hpdcache_mem_size_t'(REFILL_REQ_SIZE);
    assign mem_req_o.mem_req_command = HPDCACHE_MEM_READ;
    assign mem_req_o.mem_req_atomic = HPDCACHE_MEM_ATOMIC_ADD;
    assign mem_req_o.mem_req_cacheable = 1'b1;

    if ((HPDcacheCfg.u.mshrSets > 1) && (HPDcacheCfg.u.mshrWays > 1))
    begin : gen_mem_id_mshr_sets_and_ways_gt_1
        assign mem_req_o.mem_req_id = hpdcache_mem_id_t'({
                mshr_alloc_way_q, mshr_alloc_nline_q[0 +: HPDcacheCfg.mshrSetWidth]});
    end else if (HPDcacheCfg.u.mshrSets > 1) begin : gen_mem_id_mshr_sets_gt_1
        assign mem_req_o.mem_req_id = hpdcache_mem_id_t'(
                mshr_alloc_nline_q[0 +: HPDcacheCfg.mshrSetWidth]);
    end else if (HPDcacheCfg.u.mshrWays > 1) begin : gen_mem_id_mshr_ways_gt_1
        assign mem_req_o.mem_req_id = hpdcache_mem_id_t'(mshr_alloc_way_q);
    end else begin : gen_mem_id_mshr_sets_and_ways_eq_1
        assign mem_req_o.mem_req_id = '0;
    end

    always_ff @(posedge clk_i)
    begin : miss_req_fsm_internal_ff
        if (mshr_alloc) begin
            mshr_alloc_way_q <= mshr_alloc_way_d;
            mshr_alloc_nline_q <= mshr_alloc_nline_i;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni)
    begin : miss_req_fsm_ff
        if (!rst_ni) begin
            miss_req_fsm_q <= MISS_REQ_IDLE;
        end else begin
            miss_req_fsm_q <= miss_req_fsm_d;
        end
    end
    //  }}}

    //  Refill FSM
    //  {{{

    //      ask permission to the refill arbiter if there is a pending refill
    assign refill_req_valid_o  = refill_fsm_q == REFILL_IDLE ? refill_fifo_resp_meta_rok : 1'b0;

    always_comb
    begin : miss_resp_fsm_comb
        refill_updt_sel_victim_o = 1'b0;
        refill_set_o            = '0;
        refill_way              = '0;
        refill_write_dir_o      = 1'b0;
        refill_write_data_o     = 1'b0;
        refill_updt_rtab_o      = 1'b0;
        refill_cnt_d            = refill_cnt_q;

        inval_check_dir_o       = 1'b0;
        inval_write_dir_o       = 1'b0;

        refill_core_rsp_valid   = 1'b0;
        refill_core_rsp_sid     = '0;
        refill_core_rsp_tid     = '0;
        refill_core_rsp_error   = 1'b0;
        refill_core_rsp_word    = 0;

        refill_fifo_resp_meta_r = 1'b0;
        refill_fifo_resp_data_r = 1'b0;

        mshr_ack_cs             = 1'b0;
        mshr_ack                = 1'b0;

        refill_fsm_d            = refill_fsm_q;

        case (refill_fsm_q)
            //  Wait for refill responses
            //  {{{
            REFILL_IDLE: begin
                if (refill_fifo_resp_meta_rok) begin
                    //  anticipate the activation of the MSHR independently of the grant signal from
                    //  the refill arbiter. This is to avoid the introduction of unnecessary timing
                    //  paths (however there could be a minor augmentation of the power consumption)
                    mshr_ack_cs = ~refill_fifo_resp_meta_rdata.is_inval;

                    //  if the permission is granted, start refilling
                    if (refill_req_ready_i) begin
                        refill_set_o = mshr_ack_cache_set;

                        if (refill_fifo_resp_meta_rdata.is_inval) begin
                            //  check for a match with the line being invalidated in the cache dir
                            inval_check_dir_o = 1'b1;

                            refill_fsm_d = REFILL_INVAL;
                        end else begin
                            //  read the MSHR and reset the valid bit for the corresponding entry
                            mshr_ack = ~refill_fifo_resp_meta_rdata.is_inval;

                            //  initialize the counter for refill words
                            refill_cnt_d = 0;
                            refill_fsm_d = REFILL_WRITE;
                        end
                    end
                end
            end
            //  }}}

            //  Write refill data into the cache
            //  {{{
            REFILL_WRITE: begin
                automatic logic is_prefetch;
                automatic hpdcache_uint core_rsp_word;

                //  Respond to the core (when needed)
                if (refill_cnt_q == 0) begin
                    core_rsp_word = hpdcache_uint'(mshr_ack_word)/HPDcacheCfg.u.accessWords;

                    if (mshr_ack_need_rsp) begin
                        refill_core_rsp_valid = (hpdcache_uint'(core_rsp_word) == 0);
                    end

                    refill_core_rsp_sid = mshr_ack_src_id;
                    refill_core_rsp_tid = mshr_ack_req_id;
                    refill_core_rsp_error = refill_is_error_o;
                    refill_core_rsp_word = hpdcache_word_t'(
                        hpdcache_uint'(mshr_ack_word)/HPDcacheCfg.u.reqWords);
                end else begin
                    core_rsp_word = hpdcache_uint'(refill_core_rsp_word_q)/
                                                   HPDcacheCfg.u.accessWords;

                    if (refill_need_rsp_q) begin
                        automatic hpdcache_uint refill_cnt;
                        refill_cnt = hpdcache_uint'(refill_cnt_q)/HPDcacheCfg.u.accessWords;
                        refill_core_rsp_valid = (core_rsp_word == refill_cnt);
                    end

                    refill_core_rsp_sid = refill_sid_q;
                    refill_core_rsp_tid = refill_tid_q;
                    refill_core_rsp_error = refill_is_error_o;
                    refill_core_rsp_word = hpdcache_word_t'(
                        hpdcache_uint'(refill_core_rsp_word_q)/HPDcacheCfg.u.reqWords);
                end

                //  Write the the data in the cache data array
                if (refill_cnt_q == 0) begin
                    refill_set_o = mshr_ack_cache_set;
                    refill_way = mshr_ack_cache_way;
                    is_prefetch = mshr_ack_is_prefetch;
                end else begin
                    refill_set_o = refill_set_q;
                    refill_way = refill_way_q;
                    is_prefetch = refill_is_prefetch_q;
                end
                refill_write_data_o = ~refill_is_error_o;

                //  Consume chunk of data from the FIFO buffer in the memory interface
                refill_fifo_resp_data_r = 1'b1;

                //  Update directory on the last chunk of data
                refill_cnt_d = refill_cnt_q + hpdcache_word_t'(HPDcacheCfg.u.accessWords);

                if (hpdcache_uint'(refill_cnt_q) == REFILL_LAST_CHUNK_WORD) begin
                    if (REFILL_LAST_CHUNK_WORD == 0) begin
                        //  Special case: if the cache-line data can be written in a single cycle,
                        //  wait an additional cycle to write the directory. This allows to prevent
                        //  a RAM-to-RAM timing path between the MSHR and the DIR.
                        refill_fsm_d = REFILL_WRITE_DIR;
                    end else begin
                        //  Write the new entry in the cache directory
                        refill_write_dir_o = 1'b1;

                        //  Update the victim selection. Only in the following cases:
                        //  - There is no error in response AND
                        //  - It is a prefetch and the cfg_prefetch_updt_sel_victim_i is set OR
                        //  - It is a read miss.
                        refill_updt_sel_victim_o  =  ~refill_is_error_o &
                                                    (~is_prefetch | cfg_prefetch_updt_sel_victim_i);

                        //  Update dependency flags in the retry table
                        refill_updt_rtab_o  = 1'b1;

                        //  consume the response from the network
                        refill_fifo_resp_meta_r = 1'b1;

                        refill_fsm_d = REFILL_IDLE;
                    end
                end
            end
            //  }}}

            //  Write cache directory (this state is only visited when ACCESS_WORDS == CL_WORDS,
            //  this is when the entire cache-line can be written in a single cycle)
            //  {{{
            REFILL_WRITE_DIR: begin
                //  Select the target set and way
                refill_set_o = refill_set_q;
                refill_way = refill_way_q;

                //  Write the new entry in the cache directory
                refill_write_dir_o  = 1'b1;

                //  Update the victim selection. Only in the following cases:
                //  - There is no error in response AND
                //  - It is a prefetch and the cfg_prefetch_updt_sel_victim_i is set OR
                //  - It is a read miss.
                refill_updt_sel_victim_o  = ~refill_is_error_o &
                                           (~refill_is_prefetch_q | cfg_prefetch_updt_sel_victim_i);

                //  Update dependency flags in the retry table
                refill_updt_rtab_o = 1'b1;

                //  consume the response from the network
                refill_fifo_resp_meta_r = 1'b1;

                refill_fsm_d = REFILL_IDLE;
            end
            //  }}}

            //  Invalidate the target cacheline (if it matches a valid cacheline)
            //  {{{
            REFILL_INVAL: begin
                //  Invalidate if there is a match
                inval_write_dir_o = inval_hit_i;

                //  consume the invalidation from the network
                refill_fifo_resp_meta_r = 1'b1;

                refill_fsm_d = REFILL_IDLE;
            end

            default: begin
`ifndef HPDCACHE_ASSERT_OFF
                assert (1) $error("miss_handler: illegal state");
`endif
            end
        endcase
    end

    assign refill_is_error_o = (refill_fifo_resp_meta_rdata.r_error == HPDCACHE_MEM_RESP_NOK);

    assign refill_busy_o  = (refill_fsm_q != REFILL_IDLE);
    assign refill_nline_o = {refill_tag_q, refill_set_q};
    assign refill_word_o  = refill_cnt_q;

    assign inval_nline_o = refill_fifo_resp_meta_rdata.inval_nline;

    assign mshr_check_tag = mshr_check_nline_i[HPDcacheCfg.setWidth +: HPDcacheCfg.tagWidth];
    assign mshr_check_set = mshr_check_offset_i[HPDcacheCfg.clOffsetWidth +: HPDcacheCfg.setWidth];

    if (HPDcacheCfg.u.mshrSets > 1) begin : gen_mshr_set_gt_1
        //  MSHR ack set and way
        assign mshr_ack_set = refill_fifo_resp_meta_rdata.r_id[0 +: HPDcacheCfg.mshrSetWidth];
        if (HPDcacheCfg.u.mshrWays > 1) begin : gen_mshr_ack_way_gt_1
            assign mshr_ack_way = refill_fifo_resp_meta_rdata.r_id[HPDcacheCfg.mshrSetWidth +:
                                                                   HPDcacheCfg.mshrWayWidth];
        end else begin : gen_mshr_ack_way_eq_1
            assign mshr_ack_way = '0;
        end
    end else begin : gen_mshr_set_eq_1
        //  MSHR ack set and way
        assign mshr_ack_set = '0;
        if (HPDcacheCfg.u.mshrWays > 1) begin : gen_mshr_ack_way_gt_1
            assign mshr_ack_way = refill_fifo_resp_meta_rdata.r_id[0 +: HPDcacheCfg.mshrWayWidth];
        end else begin : gen_mshr_ack_way_eq_1
            assign mshr_ack_way = '0;
        end
    end

    //  Write the new entry in the cache directory
    //  In case of error in the refill response, invalidate pre-allocated cache directory entry
    assign refill_dir_entry_o = '{
        valid   : ~refill_is_error_o,
        wback   : ~refill_is_error_o & refill_wback_q,
        dirty   : 1'b0,
        fetch   : 1'b0,
        tag     : refill_tag_q,
        default :'0
    };

    assign refill_core_rsp.rdata   = refill_core_rsp_rdata;
    assign refill_core_rsp.sid     = refill_core_rsp_sid;
    assign refill_core_rsp.tid     = refill_core_rsp_tid;
    assign refill_core_rsp.error   = refill_core_rsp_error;
    assign refill_core_rsp.aborted = 1'b0;

    hpdcache_fifo_reg #(
        .FIFO_DEPTH  (1),
        .FEEDTHROUGH (HPDcacheCfg.u.refillCoreRspFeedthrough),
        .fifo_data_t (hpdcache_rsp_t)
    ) i_refill_core_rsp_buf(
        .clk_i,
        .rst_ni,
        .w_i         (refill_core_rsp_valid),
        .wok_o       (/*unused*/),
        .wdata_i     (refill_core_rsp),
        .r_i         (1'b1),  //  core shall always be ready to consume a response
        .rok_o       (refill_core_rsp_valid_o),
        .rdata_o     (refill_core_rsp_o)
    );

    //  refill's width is bigger than the width of the core's interface
    if (REFILL_REQ_RATIO > 1) begin : gen_core_rsp_data_mux
        hpdcache_mux #(
            .NINPUT      (REFILL_REQ_RATIO),
            .DATA_WIDTH  (HPDcacheCfg.reqDataWidth)
        ) data_read_rsp_mux_i(
            .data_i      (refill_data_o),
            .sel_i       (refill_core_rsp_word[0 +: $clog2(REFILL_REQ_RATIO)]),
            .data_o      (refill_core_rsp_rdata)
        );
    end

    //  refill's width is equal to the width of the core's interface
    else begin : gen_core_rsp_eqsize
        assign refill_core_rsp_rdata = refill_data_o;
    end

    /* FIXME: when multiple chunks, in case of error, the error bit is not
     *        necessarily set on all chunks */
    assign refill_fifo_resp_meta_wdata = '{
        r_error    : mem_resp_i.mem_resp_r_error,
        r_id       : mem_resp_i.mem_resp_r_id,
        is_inval   : mem_resp_inval_i,
        inval_nline: mem_resp_inval_nline_i
    };

    hpdcache_fifo_reg #(
        .FIFO_DEPTH  (HPDcacheCfg.u.refillFifoDepth),
        .fifo_data_t (mem_resp_metadata_t)
    ) i_r_metadata_fifo (
        .clk_i,
        .rst_ni,

        .w_i    (refill_fifo_resp_meta_w),
        .wok_o  (refill_fifo_resp_meta_wok),
        .wdata_i(refill_fifo_resp_meta_wdata),

        .r_i    (refill_fifo_resp_meta_r),
        .rok_o  (refill_fifo_resp_meta_rok),
        .rdata_o(refill_fifo_resp_meta_rdata)
    );

    hpdcache_data_resize #(
        .WR_WIDTH (HPDcacheCfg.u.memDataWidth),
        .RD_WIDTH (HPDcacheCfg.accessWidth),
        .DEPTH    (HPDcacheCfg.u.refillFifoDepth)
    ) i_data_resize(
        .clk_i,
        .rst_ni,

        .w_i    (refill_fifo_resp_data_w),
        .wok_o  (refill_fifo_resp_data_wok),
        .wdata_i(mem_resp_i.mem_resp_r_data),
        .wlast_i(mem_resp_i.mem_resp_r_last),

        .r_i    (refill_fifo_resp_data_r),
        .rok_o  (/* unused */),
        .rdata_o(refill_fifo_resp_data_rdata),
        .rlast_o(/* unused */)
    );

    assign refill_data_o = refill_fifo_resp_data_rdata;

    //      The DATA fifo is only used for refill responses
    assign refill_fifo_resp_data_w = mem_resp_valid_i &
            ((refill_fifo_resp_meta_wok | ~mem_resp_i.mem_resp_r_last) &
            ~mem_resp_inval_i);

    //      The METADATA fifo is used for both refill responses and invalidations
    assign refill_fifo_resp_meta_w = mem_resp_valid_i &
            ((refill_fifo_resp_data_wok & mem_resp_i.mem_resp_r_last) |
            mem_resp_inval_i);

    always_comb
    begin : mem_resp_ready_comb
        mem_resp_ready_o = 1'b0;
        if (mem_resp_valid_i) begin
            if (mem_resp_inval_i) begin
                mem_resp_ready_o = refill_fifo_resp_meta_wok;
            end else begin
                mem_resp_ready_o = (refill_fifo_resp_meta_wok | ~mem_resp_i.mem_resp_r_last) &
                                    refill_fifo_resp_data_wok;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni)
    begin : miss_resp_fsm_ff
        if (!rst_ni) begin
            refill_fsm_q <= REFILL_IDLE;
        end else begin
            refill_fsm_q <= refill_fsm_d;
        end
    end

    always_ff @(posedge clk_i)
    begin : miss_resp_fsm_internal_ff
        if ((refill_fsm_q == REFILL_WRITE) && (refill_cnt_q == 0)) begin
            refill_set_q <= mshr_ack_cache_set;
            refill_way_q <= mshr_ack_cache_way;
            refill_tag_q <= mshr_ack_cache_tag;
            refill_sid_q <= mshr_ack_src_id;
            refill_tid_q <= mshr_ack_req_id;
            refill_need_rsp_q <= mshr_ack_need_rsp;
            refill_is_prefetch_q <= mshr_ack_is_prefetch;
            refill_wback_q <= mshr_ack_wback;
            refill_core_rsp_word_q <= mshr_ack_word;
        end
        refill_cnt_q <= refill_cnt_d;
    end
    //  }}}
    //  }}}

    //  Miss Status Holding Register component
    //  {{{
    hpdcache_mshr #(
        .HPDcacheCfg              (HPDcacheCfg),
        .hpdcache_nline_t         (hpdcache_nline_t),
        .hpdcache_tag_t           (hpdcache_tag_t),
        .hpdcache_set_t           (hpdcache_set_t),
        .hpdcache_word_t          (hpdcache_word_t),
        .hpdcache_way_t           (hpdcache_way_t),

        .hpdcache_req_tid_t       (hpdcache_req_tid_t),
        .hpdcache_req_sid_t       (hpdcache_req_sid_t),

        .mshr_way_t               (mshr_way_t),
        .mshr_set_t               (mshr_set_t)
    ) hpdcache_mshr_i(
        .clk_i,
        .rst_ni,

        .empty_o                  (mshr_empty),
        .full_o                   (mshr_full_o),

        .check_i                  (mshr_check_i),
        .check_set_i              (mshr_check_set),
        .check_tag_i              (mshr_check_tag),
        .hit_o                    (mshr_check_hit_o),
        .alloc_i                  (mshr_alloc),
        .alloc_cs_i               (mshr_alloc_cs),
        .alloc_nline_i            (mshr_alloc_nline_i),
        .alloc_req_id_i           (mshr_alloc_tid_i),
        .alloc_src_id_i           (mshr_alloc_sid_i),
        .alloc_word_i             (mshr_alloc_word_i),
        .alloc_victim_way_i       (mshr_alloc_victim_way),
        .alloc_need_rsp_i         (mshr_alloc_need_rsp_i),
        .alloc_is_prefetch_i      (mshr_alloc_is_prefetch_i),
        .alloc_wback_i            (mshr_alloc_wback_i),
        .alloc_full_o             (mshr_alloc_full_o),
        .alloc_way_o              (mshr_alloc_way_d),

        .ack_i                    (mshr_ack),
        .ack_cs_i                 (mshr_ack_cs),
        .ack_set_i                (mshr_ack_set),
        .ack_way_i                (mshr_ack_way),
        .ack_req_id_o             (mshr_ack_req_id),
        .ack_src_id_o             (mshr_ack_src_id),
        .ack_cache_set_o          (mshr_ack_cache_set),
        .ack_cache_way_o          (mshr_ack_cache_way),
        .ack_cache_tag_o          (mshr_ack_cache_tag),
        .ack_word_o               (mshr_ack_word),
        .ack_need_rsp_o           (mshr_ack_need_rsp),
        .ack_is_prefetch_o        (mshr_ack_is_prefetch),
        .ack_wback_o              (mshr_ack_wback)
    );

    hpdcache_1hot_to_binary #(.N(HPDcacheCfg.u.ways)) victim_way_encoder_i(
        .val_i(mshr_alloc_victim_way_i),
        .val_o(mshr_alloc_victim_way)
    );

    hpdcache_decoder #(.N(HPDcacheCfg.wayIndexWidth)) victim_way_decoder_i(
        .en_i (refill_busy_o),
        .val_i(refill_way),
        .val_o(refill_way_o)
    );

    //    Indicate to the cache controller that there is no pending miss. This
    //    is, when the MSHR is empty, and the MISS handler has finished of
    //    processing the last miss response.
    assign mshr_empty_o = mshr_empty & ~refill_busy_o;
    //  }}}

    //  Assertions
    //  {{{
`ifndef HPDCACHE_ASSERT_OFF
`endif
    //  }}}

endmodule
//  }}}
