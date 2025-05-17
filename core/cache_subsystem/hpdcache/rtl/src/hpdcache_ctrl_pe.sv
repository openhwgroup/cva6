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
 *  Description   : HPDcache Control Protocol Engine
 *  History       :
 */
module hpdcache_ctrl_pe
    // Ports
    // {{{
(
    //   Requests
    //   {{{
    input  logic                   core_req_valid_i,
    output logic                   core_req_ready_o,

    input  logic                   rtab_req_valid_i,
    output logic                   rtab_req_ready_o,

    input  logic                   refill_req_valid_i,
    output logic                   refill_req_ready_o,
    //   }}}

    //   Pipeline stage 0
    //   {{{
    input  logic                   st0_req_is_error_i,
    input  logic                   st0_req_is_uncacheable_i,
    input  logic                   st0_req_need_rsp_i,
    input  logic                   st0_req_is_load_i,
    input  logic                   st0_req_is_store_i,
    input  logic                   st0_req_is_amo_i,
    input  logic                   st0_req_is_cmo_fence_i,
    input  logic                   st0_req_is_cmo_inval_i,
    input  logic                   st0_req_is_cmo_prefetch_i,
    output logic                   st0_req_mshr_check_o,
    output logic                   st0_req_cachedir_read_o,
    output logic                   st0_req_cachedata_read_o,
    //   }}}

    //   Pipeline stage 1
    //   {{{
    input  logic                   st1_req_valid_i,
    input  logic                   st1_req_abort_i,
    input  logic                   st1_req_rtab_i,
    input  logic                   st1_req_is_error_i,
    input  logic                   st1_req_is_uncacheable_i,
    input  logic                   st1_req_need_rsp_i,
    input  logic                   st1_req_is_load_i,
    input  logic                   st1_req_is_store_i,
    input  logic                   st1_req_is_amo_i,
    input  logic                   st1_req_is_cmo_inval_i,
    input  logic                   st1_req_is_cmo_flush_i,
    input  logic                   st1_req_is_cmo_fence_i,
    input  logic                   st1_req_is_cmo_prefetch_i,
    input  logic                   st1_req_wr_wt_i,
    input  logic                   st1_req_wr_wb_i,
    input  logic                   st1_req_wr_auto_i,
    input  logic                   st1_dir_hit_wback_i,
    input  logic                   st1_dir_hit_dirty_i,
    input  logic                   st1_dir_hit_fetch_i,
    input  logic                   st1_dir_victim_unavailable_i,
    input  logic                   st1_dir_victim_valid_i,
    input  logic                   st1_dir_victim_wback_i,
    input  logic                   st1_dir_victim_dirty_i,
    output logic                   st1_req_valid_o,
    output logic                   st1_req_is_error_o,
    output logic                   st1_rsp_valid_o,
    output logic                   st1_rsp_error_o,
    output logic                   st1_rsp_aborted_o,
    output logic                   st1_req_cachedir_sel_victim_o,
    output logic                   st1_req_cachedir_updt_sel_victim_o,
    output logic                   st1_req_cachedata_write_o,
    output logic                   st1_req_cachedata_write_enable_o,
    input  logic                   st1_mshr_alloc_ready_i,
    input  logic                   st1_mshr_hit_i,
    input  logic                   st1_mshr_full_i,
    //   }}}

    //   Pipeline stage 2
    //   {{{
    input  logic                   st2_mshr_alloc_i,
    input  logic                   st2_mshr_alloc_is_prefetch_i,
    input  logic                   st2_mshr_alloc_wback_i,
    output logic                   st2_mshr_alloc_o,
    output logic                   st2_mshr_alloc_cs_o,
    output logic                   st2_mshr_alloc_need_rsp_o,
    output logic                   st2_mshr_alloc_wback_o,

    input  logic                   st2_dir_updt_i,
    input  logic                   st2_dir_updt_valid_i,
    input  logic                   st2_dir_updt_wback_i,
    input  logic                   st2_dir_updt_dirty_i,
    input  logic                   st2_dir_updt_fetch_i,
    output logic                   st2_dir_updt_o,
    output logic                   st2_dir_updt_valid_o,
    output logic                   st2_dir_updt_wback_o,
    output logic                   st2_dir_updt_dirty_o,
    output logic                   st2_dir_updt_fetch_o,
    //   }}}

    //   Replay
    //   {{{
    input  logic                   rtab_full_i,
    input  logic                   rtab_fence_i,
    output logic                   rtab_check_o,
    input  logic                   rtab_check_hit_i,
    output logic                   st1_rtab_alloc_o,
    output logic                   st1_rtab_alloc_and_link_o,
    output logic                   st1_rtab_commit_o,
    output logic                   st1_rtab_rback_o,
    output logic                   st1_rtab_mshr_hit_o,
    output logic                   st1_rtab_mshr_full_o,
    output logic                   st1_rtab_mshr_ready_o,
    output logic                   st1_rtab_write_miss_o,
    output logic                   st1_rtab_wbuf_hit_o,
    output logic                   st1_rtab_wbuf_not_ready_o,
    output logic                   st1_rtab_dir_unavailable_o,
    output logic                   st1_rtab_dir_fetch_o,
    output logic                   st1_rtab_flush_hit_o,
    output logic                   st1_rtab_flush_not_ready_o,
    //   }}}

    //   Cache directory
    //   {{{
    input  logic                   cachedir_hit_i,
    input  logic                   cachedir_init_ready_i,
    //   }}}

    //   Refill interface
    //   {{{
    input  logic                   refill_busy_i,
    input  logic                   refill_core_rsp_valid_i,
    //   }}}

    //   Write buffer
    //   {{{
    input  logic                   wbuf_write_ready_i,
    input  logic                   wbuf_read_hit_i,
    output logic                   wbuf_write_valid_o,
    output logic                   wbuf_write_uncacheable_o,
    output logic                   wbuf_read_flush_hit_o,
    //   }}}

    //   Flush controller
    input  logic                   flush_busy_i,
    input  logic                   st1_flush_check_hit_i,
    input  logic                   st1_flush_alloc_ready_i,
    input  logic                   st2_flush_alloc_i,
    output logic                   st2_flush_alloc_o,

    //   Uncacheable request handler
    //   {{{
    input  logic                   uc_busy_i,
    output logic                   uc_req_valid_o,
    output logic                   uc_core_rsp_ready_o,
    //   }}}

    //   Cache Management Operation (CMO)
    //   {{{
    input  logic                   cmo_busy_i,
    input  logic                   cmo_wait_i,
    output logic                   cmo_req_valid_o,
    output logic                   cmo_core_rsp_ready_o,
    //   }}}

    //   Configuration
    //   {{{
    input  logic                   cfg_prefetch_updt_plru_i,
    input  logic                   cfg_default_wb_i,
    //   }}}

    //   Performance events
    //   {{{
    output logic                   evt_cache_write_miss_o,
    output logic                   evt_cache_read_miss_o,
    output logic                   evt_uncached_req_o,
    output logic                   evt_cmo_req_o,
    output logic                   evt_write_req_o,
    output logic                   evt_read_req_o,
    output logic                   evt_prefetch_req_o,
    output logic                   evt_req_on_hold_o,
    output logic                   evt_rtab_rollback_o,
    output logic                   evt_stall_refill_o,
    output logic                   evt_stall_o
    //   }}}
);
    // }}}

    //  Definition of internal signals
    //  {{{
    logic  st1_fence;
    logic  st1_rtab_alloc, st1_rtab_alloc_and_link;
    //  }}}

    //  Global control signals
    //  {{{

    //  Determine if the new request is a "fence". Here, fence instructions are
    //  considered those that need to be executed in program order
    //  (irrespectively of addresses). This means that all memory operations
    //  arrived before the "fence" instruction need to be finished, and only
    //  then the "fence" instruction is executed. In the same manner, all
    //  instructions following the "fence" need to wait the completion of this
    //  last before being executed.
    assign st1_fence = st1_req_is_uncacheable_i |
                       st1_req_is_cmo_fence_i   |
                       st1_req_is_cmo_inval_i   |
                       st1_req_is_cmo_flush_i;

    //      Trigger an event signal when a new request cannot consumed
    assign evt_stall_o = core_req_valid_i & ~core_req_ready_o;
    //  }}}

    //  Arbitration of responses to the core
    //  {{{
    assign uc_core_rsp_ready_o  = ~refill_core_rsp_valid_i;
    assign cmo_core_rsp_ready_o = ~refill_core_rsp_valid_i;
    //  }}}

    //  Replay logic
    //  {{{
    //      Replay table allocation
    assign st1_rtab_alloc_o          = st1_rtab_alloc          & ~st1_req_rtab_i,
           st1_rtab_alloc_and_link_o = st1_rtab_alloc_and_link,
           st1_rtab_rback_o          = st1_rtab_alloc          &  st1_req_rtab_i;

    //      Performance event
    assign evt_req_on_hold_o   = st1_rtab_alloc | st1_rtab_alloc_and_link,
           evt_rtab_rollback_o = st1_rtab_rback_o;
    //  }}}

    //  Data-cache control lines
    //  {{{
    always_comb
    begin : hpdcache_ctrl_comb
        automatic logic nop;
        automatic logic st1_nop; //  Do not consume a request in stage 0 because of stage 1 hazard
        automatic logic st2_nop; //  Do not consume a request in stage 0 because of stage 2 haward
        automatic logic st1_req_is_cacheable_store;


        uc_req_valid_o                      = 1'b0;

        cmo_req_valid_o                     = 1'b0;

        wbuf_write_valid_o                  = 1'b0;
        wbuf_read_flush_hit_o               = 1'b0;
        wbuf_write_uncacheable_o            = 1'b0; // unused

        core_req_ready_o                    = 1'b0;
        rtab_req_ready_o                    = 1'b0;
        refill_req_ready_o                  = 1'b0;

        st0_req_mshr_check_o                = 1'b0;
        st0_req_cachedir_read_o             = 1'b0;
        st0_req_cachedata_read_o            = 1'b0;

        st1_req_valid_o                     = st1_req_valid_i;
        st1_req_is_error_o                  = st1_req_is_error_i;
        st1_req_is_cacheable_store          = 1'b0;
        st1_nop                             = 1'b0;
        st1_req_cachedata_write_o           = 1'b0;
        st1_req_cachedata_write_enable_o    = 1'b0;
        st1_req_cachedir_sel_victim_o       = 1'b0;
        st1_req_cachedir_updt_sel_victim_o  = 1'b0;
        st1_rsp_valid_o                     = 1'b0;
        st1_rsp_error_o                     = 1'b0;
        st1_rsp_aborted_o                   = 1'b0;

        st2_mshr_alloc_o                    = st2_mshr_alloc_i;
        st2_mshr_alloc_cs_o                 = 1'b0;
        st2_mshr_alloc_need_rsp_o           = 1'b0;
        st2_mshr_alloc_wback_o              = st2_mshr_alloc_wback_i;

        st2_flush_alloc_o                   = st2_flush_alloc_i;

        st2_dir_updt_o                      = st2_dir_updt_i;
        st2_dir_updt_valid_o                = st2_dir_updt_valid_i;
        st2_dir_updt_wback_o                = st2_dir_updt_wback_i;
        st2_dir_updt_dirty_o                = st2_dir_updt_dirty_i;
        st2_dir_updt_fetch_o                = st2_dir_updt_fetch_i;

        st2_nop                             = 1'b0;

        nop                                 = 1'b0;

        rtab_check_o                        = 1'b0;
        st1_rtab_alloc                      = 1'b0;
        st1_rtab_alloc_and_link             = 1'b0;
        st1_rtab_commit_o                   = 1'b0;
        st1_rtab_mshr_hit_o                 = 1'b0;
        st1_rtab_mshr_full_o                = 1'b0;
        st1_rtab_mshr_ready_o               = 1'b0;
        st1_rtab_write_miss_o               = 1'b0;
        st1_rtab_wbuf_hit_o                 = 1'b0;
        st1_rtab_wbuf_not_ready_o           = 1'b0;
        st1_rtab_dir_unavailable_o          = 1'b0;
        st1_rtab_dir_fetch_o                = 1'b0;
        st1_rtab_flush_hit_o                = 1'b0;
        st1_rtab_flush_not_ready_o          = 1'b0;

        evt_cache_write_miss_o              = 1'b0;
        evt_cache_read_miss_o               = 1'b0;
        evt_uncached_req_o                  = 1'b0;
        evt_cmo_req_o                       = 1'b0;
        evt_write_req_o                     = 1'b0;
        evt_read_req_o                      = 1'b0;
        evt_prefetch_req_o                  = 1'b0;
        evt_stall_refill_o                  = 1'b0;

        //  Wait for the cache to be initialized
        //  {{{
        if (!cachedir_init_ready_i) begin
            //  initialization of the cache RAMs
        end
        //  }}}

        //  Refilling the cache
        //  {{{
        else if (refill_busy_i) begin
            //  miss handler has the control of the cache pipeline
            evt_stall_refill_o = core_req_valid_i;
        end
        //  }}}

        //  Flush controller reading the cache
        //  {{{
        else if (flush_busy_i) begin
            //  flush controller has the control of the cache pipeline
        end
        //  }}}

        //  Normal pipeline operation
        //  {{{
        else begin
            //  Stage 2 request pending
            //  {{{
            //  Allocate an entry in the MSHR
            if (st2_mshr_alloc_i) begin
                //  Reset mshr alloc request
                st2_mshr_alloc_o = 1'b0;

                //  Enable the MSHR
                st2_mshr_alloc_cs_o = 1'b1;

                //  Introduce a NOP in the next cycle to prevent a hazard on the MSHR
                st2_nop = 1'b1;

                //  Performance event
                evt_cache_read_miss_o = ~st2_mshr_alloc_is_prefetch_i;
                evt_read_req_o        = ~st2_mshr_alloc_is_prefetch_i;
                evt_prefetch_req_o    =  st2_mshr_alloc_is_prefetch_i;
            end

            //  Flush a cacheline
            if (st2_flush_alloc_i) begin
                //  Reset cache directory update request
                st2_flush_alloc_o = 1'b0;

                //  Introduce a NOP in the next cycle to prevent a hazard on the cache data
                st2_nop = 1'b1;
            end

            //  Update the cache directory
            if (st2_dir_updt_i) begin
                //  Reset cache directory update request
                st2_dir_updt_o = 1'b0;

                //  Introduce a NOP in the next cycle to prevent a hazard on the cache dir
                st2_nop = 1'b1;
            end
            //  }}}

            //  Stage 1 request pending
            //  {{{
            if (st1_req_valid_i) begin
                //  Check if the request in stage 1 has a conflict with one of the
                //  request in the replay table.
                rtab_check_o = ~st1_req_rtab_i & ~st1_fence;

                //  Check if the current request is aborted. If so, respond to the
                //  core (when need_rsp is set) and set the aborted flag
                if (st1_req_abort_i && !st1_req_rtab_i) begin
                    st1_rsp_valid_o = st1_req_need_rsp_i;
                    st1_rsp_aborted_o = 1'b1;
                end

                else if (st1_req_is_error_i) begin
                    st1_rtab_commit_o = st1_req_rtab_i;
                    st1_rsp_valid_o = st1_req_need_rsp_i;
                    st1_rsp_error_o = st1_req_need_rsp_i;

                    //  Performance event
                    evt_write_req_o = st1_req_is_store_i;
                end

                //  Allocate a new entry in the replay table in case of conflict with
                //  an on-hold request
                else if (rtab_check_o && rtab_check_hit_i) begin
                    st1_rtab_alloc_and_link = 1'b1;

                    st1_nop = 1'b1;
                end

                //  CMO fence or invalidate
                //  {{{
                else if (st1_req_is_cmo_inval_i ||
                         st1_req_is_cmo_flush_i ||
                         st1_req_is_cmo_fence_i)
                begin
                    cmo_req_valid_o = 1'b1;
                    st1_nop         = 1'b1;

                    //  Performance event
                    evt_cmo_req_o = 1'b1;
                end
                //  }}}

                //  Uncacheable load, store or AMO request
                //  {{{
                else if (st1_req_is_uncacheable_i) begin
                    uc_req_valid_o = 1'b1;
                    st1_nop        = 1'b1;

                    //  Performance event
                    evt_uncached_req_o = 1'b1;
                end
                //  }}}

                //  Cacheable request
                //  {{{
                else begin
                    //  AMO cacheable request
                    //  {{{
                    if (st1_req_is_amo_i) begin
                        //  Flush required but the controller is not ready
                        if (cachedir_hit_i && st1_dir_hit_dirty_i && !st1_flush_alloc_ready_i)
                        begin
                            st1_rtab_alloc = 1'b1;
                            st1_rtab_flush_not_ready_o = 1'b1;
                            st1_nop = 1'b1;
                        end

                        //  Process the AMO request
                        else begin
                            uc_req_valid_o = 1'b1;
                            st1_nop = 1'b1;

                            //  If the request comes from the replay table, free the
                            //  corresponding RTAB entry
                            st1_rtab_commit_o = st1_req_rtab_i;

                            if (cachedir_hit_i) begin
                                //  When the hit cacheline is dirty, flush its data to the memory
                                st2_flush_alloc_o = st1_dir_hit_dirty_i;

                                //  Update the directory: an AMO request clears the dirty bit
                                //  because it triggers a flush of the cacheline before actually
                                //  executing the AMO.
                                //  An AMO does not set the dirty bit because it is always forwarded
                                //  to the memory. Then the local copy is updated with respect
                                //  to the old data from the memory.
                                st2_dir_updt_o = 1'b1;
                                st2_dir_updt_valid_o = 1'b1;
                                st2_dir_updt_wback_o = st1_dir_hit_wback_i;
                                st2_dir_updt_dirty_o = 1'b0;

                                //  If the cacheline has been pre-allocated for a pending miss, keep
                                //  the fetch bit set
                                st2_dir_updt_fetch_o = st1_dir_hit_fetch_i;
                            end

                            //  Performance event
                            evt_uncached_req_o = 1'b1;
                        end
                    end
                    //  }}}

                    //  Load cacheable request
                    //  {{{
                    if (|{st1_req_is_load_i,
                          st1_req_is_cmo_prefetch_i})
                    begin
                        //  Cache miss
                        //  {{{
                        if (!cachedir_hit_i) begin
                            //  A cache miss inserts a nop into the pipeline
                            st1_nop = 1'b1;

                            //  If there is a match in the write buffer, send the entry right away
                            wbuf_read_flush_hit_o = 1'b1;

                            //  Select a victim cacheline
                            st1_req_cachedir_sel_victim_o = 1'b1;

                            //  Pending miss on the same line
                            if (st1_mshr_hit_i) begin
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_mshr_hit_o = 1'b1;
                            end

                            //  No available slot in the MSHR
                            else if (st1_mshr_full_i) begin
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_mshr_full_o = 1'b1;
                            end

                            //  All entries in the target set are being fetched
                            else if (st1_dir_victim_unavailable_i) begin
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_dir_unavailable_o = 1'b1;
                            end

                            //  Hit on an open entry of the write buffer: wait for the entry to be
                            //  acknowledged
                            else if (wbuf_read_hit_i) begin
                                //  Put the request in the replay table
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_wbuf_hit_o = 1'b1;
                            end

                            //  Miss Handler is not ready to send
                            else if (!st1_mshr_alloc_ready_i) begin
                                //  Put the request on hold if the MISS HANDLER is not
                                //  ready to send a new miss request. This is to prevent
                                //  a deadlock between the read request channel and the
                                //  read response channel.
                                //
                                //  The request channel may be stalled by targets if they
                                //  are not able to send a response (response is
                                //  prioritary). Therefore, we need to put the request on
                                //  hold to allow a possible refill read response to be
                                //  accomplished.
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_mshr_ready_o = 1'b1;
                            end

                            //  Flush pending on the miss cacheline
                            else if (st1_flush_check_hit_i) begin
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_flush_hit_o = 1'b1;
                            end

                            //  Flush needed but the controller is not ready
                            else if (st1_dir_victim_dirty_i && !st1_flush_alloc_ready_i) begin
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_flush_not_ready_o = 1'b1;
                            end

                            //  Forward the request to the next stage to allocate the
                            //  entry in the MSHR and send the refill request
                            else begin
                                //  When the victim cacheline is dirty, flush its data to the
                                //  memory
                                st2_flush_alloc_o = st1_dir_victim_dirty_i;

                                //  If the request comes from the replay table, free the
                                //  corresponding RTAB entry
                                st1_rtab_commit_o = st1_req_rtab_i;

                                //  Request a MSHR allocation
                                st2_mshr_alloc_o = 1'b1;
                                st2_mshr_alloc_need_rsp_o = st1_req_need_rsp_i;
                                st2_mshr_alloc_wback_o = (st1_req_wr_auto_i & cfg_default_wb_i) |
                                                          st1_req_wr_wb_i;

                                //  Update the cache directory state to FETCHING
                                st2_dir_updt_o = 1'b1;
                                st2_dir_updt_valid_o = st1_dir_victim_valid_i;
                                st2_dir_updt_wback_o = st1_dir_victim_wback_i;
                                st2_dir_updt_dirty_o = 1'b0;
                                st2_dir_updt_fetch_o = 1'b1;
                            end
                        end
                        //  }}}

                        //  Cache hit
                        //  {{{
                        else begin
                            //  Flush needed but the controller is not ready
                            if (st1_req_wr_wt_i && st1_dir_hit_wback_i &&
                                st1_dir_hit_dirty_i && !st1_flush_alloc_ready_i)
                            begin
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_flush_not_ready_o = 1'b1;
                                st1_nop = 1'b1;
                            end

                            //  Process the load
                            else begin
                                //  If the request comes from the replay table, free the
                                //  corresponding RTAB entry
                                st1_rtab_commit_o = st1_req_rtab_i;

                                //  Add a NOP when replaying a request, and there is no available
                                //  request from the replay table.
                                st1_nop = st1_req_rtab_i & ~rtab_req_valid_i;

                                //  Update victim selection for the accessed set
                                st1_req_cachedir_updt_sel_victim_o =
                                    ~st1_req_is_cmo_prefetch_i |
                                     cfg_prefetch_updt_plru_i;

                                //  Respond to the core (if needed)
                                st1_rsp_valid_o = st1_req_need_rsp_i;

                                //  Performance event
                                evt_read_req_o = ~st1_req_is_cmo_prefetch_i;
                                evt_prefetch_req_o = st1_req_is_cmo_prefetch_i;

                                //  If the cacheline is currently pre-allocated to be replaced, we
                                //  can only forward the data, but no state update is allowed.
                                if (!st1_dir_hit_fetch_i) begin
                                    //  Hint is write-through but the current state is not. The
                                    //  controller needs to update the state of the cacheline to WT
                                    if (st1_req_wr_wt_i && st1_dir_hit_wback_i) begin
                                        //  Update the directory state of the cacheline to WT
                                        st2_dir_updt_o = 1'b1;
                                        st2_dir_updt_valid_o = 1'b1;
                                        st2_dir_updt_wback_o = 1'b0;
                                        st2_dir_updt_dirty_o = 1'b0;
                                        st2_dir_updt_fetch_o = 1'b0;

                                        //  Cacheline is dirty, flush its data to the memory
                                        st2_flush_alloc_o = st1_dir_hit_dirty_i;

                                        st1_nop = 1'b1;
                                    end

                                    //  Hint is write-back but the current state is not. The
                                    //  controller needs to update the state of the cacheline to WB
                                    //  (clean)
                                    if (st1_req_wr_wb_i && !st1_dir_hit_wback_i) begin
                                        //  Update the directory state of the cacheline to WB
                                        st2_dir_updt_o = 1'b1;
                                        st2_dir_updt_valid_o = 1'b1;
                                        st2_dir_updt_wback_o = 1'b1;
                                        st2_dir_updt_dirty_o = 1'b0;
                                        st2_dir_updt_fetch_o = 1'b0;

                                        st1_nop = 1'b1;
                                    end
                                end
                            end
                        end
                        //  }}}
                    end
                    //  }}}

                    //  Store cacheable request
                    //  {{{
                    if (st1_req_is_store_i) begin
                        //  Add a NOP in the pipeline when:
                        //  - Structural hazard on the cache data if the st0 request is a load
                        //    operation.
                        //  - Replaying a request, the cache cannot accept a request from the
                        //    core the next cycle. It can however accept a new request from the
                        //    replay table
                        //
                        //  IMPORTANT: we could remove the NOP in the first scenario if the
                        //  controller checks for the hit of this write. However, this adds
                        //  a DIR_RAM -> DATA_RAM timing path.
                        st1_nop = ((core_req_valid_i |  rtab_req_valid_i) & st0_req_is_load_i) |
                                   (st1_req_rtab_i   & ~rtab_req_valid_i);

                        //  Enable the data RAM in case of write. However, the actual write
                        //  depends on the hit signal from the cache directory.
                        //
                        //  IMPORTANT: this produces unnecessary power consumption in case of
                        //  write misses, but removes timing paths between the cache directory
                        //  RAM and the data RAM chip-select.
                        st1_req_cachedata_write_o = 1'b1;

                        //  Pending miss on the same line
                        if (st1_mshr_hit_i) begin
                            //  Put the request in the replay table
                            st1_rtab_alloc = 1'b1;
                            st1_rtab_mshr_hit_o = 1'b1;

                            st1_nop = 1'b1;
                        end

                        //  Hit in the flush controller
                        else if (st1_flush_check_hit_i) begin
                            //  Put the request in the replay table
                            st1_rtab_alloc = 1'b1;
                            st1_rtab_flush_hit_o = 1'b1;

                            st1_nop = 1'b1;
                        end

                        //  Cache miss
                        //  {{{
                        else if (!cachedir_hit_i) begin
                            //  Write is write-back
                            //  {{{
                            if (st1_req_wr_wb_i || (st1_req_wr_auto_i && cfg_default_wb_i))
                            begin
                                //  Select a victim cacheline
                                st1_req_cachedir_sel_victim_o = 1'b1;

                                //  If there is a match in the write buffer, send the entry right
                                //  away
                                wbuf_read_flush_hit_o = 1'b1;

                                //  Add a nop as the next cycle the controller needs to write in the
                                //  MSHR and the directory
                                st1_nop = 1'b1;

                                //  Miss Handler is not ready to send
                                if (!st1_mshr_alloc_ready_i) begin
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_mshr_ready_o = 1'b1;
                                end

                                //  No available slot in the MSHR
                                else if (st1_mshr_full_i) begin
                                    //  Put the request in the replay table
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_mshr_full_o = 1'b1;
                                end

                                //  Hit on an entry of the write buffer: wait for the entry to be
                                //  acknowledged
                                else if (wbuf_read_hit_i) begin
                                    //  Put the request in the replay table
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_wbuf_hit_o = 1'b1;
                                end

                                //  no available victim cacheline (all currently pre-allocated and
                                //  waiting to be refilled)
                                else if (st1_dir_victim_unavailable_i) begin
                                    //  Put the request in the replay table
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_dir_unavailable_o = 1'b1;
                                end

                                //  Flush needed but the controller is not ready
                                else if (st1_dir_victim_dirty_i && !st1_flush_alloc_ready_i) begin
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_flush_not_ready_o = 1'b1;
                                end

                                else begin
                                    //  When the victim cacheline is dirty, flush its data to the
                                    //  memory
                                    st2_flush_alloc_o = st1_dir_victim_dirty_i;

                                    //  Update the directory state of the cacheline to FETCHING
                                    st2_dir_updt_o = 1'b1;
                                    st2_dir_updt_valid_o = st1_dir_victim_valid_i;
                                    st2_dir_updt_wback_o = st1_dir_victim_wback_i;
                                    st2_dir_updt_dirty_o = 1'b0;
                                    st2_dir_updt_fetch_o = 1'b1;

                                    //  Send a miss request to the memory (write-allocate)
                                    st2_mshr_alloc_o = 1'b1;
                                    st2_mshr_alloc_need_rsp_o = 1'b0;
                                    st2_mshr_alloc_wback_o = 1'b1;
                                    // FIXME Optimization: ask here the miss handler to set the
                                    //       dirty bit when the new cacheline is refilled to avoid
                                    //       the update penalty of the pending write
                                    // st2_mshr_alloc_dirty_o = 1'b1

                                    //  Put the request in the replay table
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_write_miss_o = 1'b1;

                                    //  Performance event
                                    evt_cache_write_miss_o = 1'b1;
                                end
                            end
                            //  }}}

                            //  Write is write-through
                            //  {{{
                            else begin
                                //  Request write into the write-buffer
                                wbuf_write_valid_o = 1'b1;

                                //  No available entry in the write buffer (or conflict on pending
                                //  entry)
                                if (!wbuf_write_ready_i) begin
                                    //  Put the request in the replay table
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_wbuf_not_ready_o = 1'b1;

                                    st1_nop = 1'b1;
                                end

                                else begin
                                    //  If the request comes from the replay table, free the
                                    //  corresponding RTAB entry
                                    st1_rtab_commit_o = st1_req_rtab_i;

                                    //  Respond to the core (if needed)
                                    st1_rsp_valid_o = st1_req_need_rsp_i;

                                    //  Performance event
                                    evt_cache_write_miss_o = 1'b1;
                                    evt_write_req_o        = 1'b1;
                                end
                            end
                            //  }}}
                        end
                        //  }}}

                        //  Cache hit
                        //  {{{
                        else begin
                            //  The target cacheline is pre-allocated to be replaced. Put this write
                            //  on-hold
                            if (st1_dir_hit_fetch_i) begin
                                //  Put the request in the replay table
                                st1_rtab_alloc = 1'b1;
                                st1_rtab_dir_fetch_o = 1'b1;

                                st1_nop = 1'b1;
                            end

                            //  Write is write-back
                            //  {{{
                            else if (st1_req_wr_wb_i || (st1_req_wr_auto_i && st1_dir_hit_wback_i))
                            begin
                                //  If there is a match in the write buffer, send the entry right
                                //  away
                                wbuf_read_flush_hit_o = 1'b1;

                                //  Hit on an entry of the write buffer: wait for the entry to be
                                //  acknowledged.
                                //
                                //  This check is to avoid a possible future race when flushing
                                //  a dirty cacheline if there is a pending write in the write
                                //  buffer concerning the same cacheline
                                if (wbuf_read_hit_i) begin
                                    //  Put the request in the replay table
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_wbuf_hit_o = 1'b1;
                                    st1_nop = 1'b1;

                                end else begin
                                    // Update the directory state of the cacheline to dirty
                                    if (!st1_dir_hit_wback_i || !st1_dir_hit_dirty_i) begin
                                        st2_dir_updt_o       = 1'b1;
                                        st2_dir_updt_valid_o = 1'b1;
                                        st2_dir_updt_wback_o = 1'b1;
                                        st2_dir_updt_dirty_o = 1'b1;
                                        st2_dir_updt_fetch_o = 1'b0;

                                        st1_nop = 1'b1;
                                    end

                                    //  If the request comes from the replay table, free the
                                    //  corresponding RTAB entry
                                    st1_rtab_commit_o = st1_req_rtab_i;

                                    //  Respond to the core
                                    st1_rsp_valid_o = st1_req_need_rsp_i;

                                    //  Write in the data RAM
                                    st1_req_cachedata_write_enable_o = 1'b1;

                                    //  Update victim selection for the accessed set
                                    st1_req_cachedir_updt_sel_victim_o = 1'b1;

                                    //  Performance event
                                    evt_write_req_o = 1'b1;
                                end
                            end
                            //  }}}

                            //  Write is write-through
                            //  {{{
                            else begin
                                //  Write in the write buffer unless we need to flush the cacheline
                                //  first
                                wbuf_write_valid_o = ~st1_dir_hit_dirty_i;

                                //  The cache needs to flush the cacheline but the flush controller
                                //  is not ready
                                if (st1_dir_hit_dirty_i && !st1_flush_alloc_ready_i) begin
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_flush_not_ready_o = 1'b1;

                                    st1_nop = 1'b1;
                                end

                                //  Flush the cacheline but keep it in the cache
                                else if (st1_dir_hit_dirty_i) begin
                                    //  Flush cacheline data to the memory
                                    st2_flush_alloc_o = 1'b1;

                                    //  Update the state to WT in the directory
                                    st2_dir_updt_o = 1'b1;
                                    st2_dir_updt_valid_o = 1'b1;
                                    st2_dir_updt_wback_o = 1'b0;
                                    st2_dir_updt_dirty_o = 1'b0;
                                    st2_dir_updt_fetch_o = 1'b0;

                                    //  Put the request in the replay table while waiting for the
                                    //  memory flushing
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_flush_hit_o = 1'b1;

                                    st1_nop = 1'b1;
                                end

                                //  No available entry in the write buffer (or conflict on pending
                                //  entry)
                                else if (!wbuf_write_ready_i) begin
                                    //  Put the request in the replay table
                                    st1_rtab_alloc = 1'b1;
                                    st1_rtab_wbuf_not_ready_o = 1'b1;

                                    st1_nop = 1'b1;
                                end

                                //  The store can be performed in the write buffer and in the cache
                                else begin
                                    //  If the request comes from the replay table, free the
                                    //  corresponding RTAB entry
                                    st1_rtab_commit_o = st1_req_rtab_i;

                                    //  Respond to the core
                                    st1_rsp_valid_o = st1_req_need_rsp_i;

                                    //  Update victim selection for the accessed set
                                    st1_req_cachedir_updt_sel_victim_o = 1'b1;

                                    //  Write in the data RAM
                                    st1_req_cachedata_write_enable_o = 1'b1;

                                    //  Performance event
                                    evt_write_req_o = 1'b1;
                                end
                            end
                            //  }}}
                        end
                        //  }}}
                    end
                    //  }}}
                end
                // }}}
            end
            //  }}}

            //  New request
            //  {{{
            nop = st1_nop | st2_nop;

            //     New requests/refill are served according to the following priority:
            //     0 - Refills/Invalidations (Highest priority)
            //     1 - Replay Table
            //     2 - Core (Lowest priority)

            //     * IMPORTANT: When the replay table is full, the cache
            //       cannot accept new core requests to prevent a deadlock: If
            //       the core request needs to be put on hold, as there is no
            //       place the replay table, the pipeline needs to stall. If
            //       the pipeline is stalled, dependencies of on-hold requests
            //       cannot be solved, creating a deadlock
            core_req_ready_o = core_req_valid_i
                               & ~rtab_req_valid_i
                               & ~refill_req_valid_i
                               & ~rtab_full_i
                               & ~cmo_busy_i
                               & ~uc_busy_i
                               & ~rtab_fence_i
                               & ~nop;

            rtab_req_ready_o = rtab_req_valid_i
                               & ~refill_req_valid_i
                               & (~cmo_busy_i | cmo_wait_i)
                               & ~nop;

            refill_req_ready_o = refill_req_valid_i
                                 & (~cmo_busy_i | cmo_wait_i)
                                 & ~st1_req_valid_i
                                 & ~(st2_mshr_alloc_i | st2_dir_updt_i);

            //      Forward the core/rtab request to stage 1
            st1_req_valid_o = core_req_ready_o | rtab_req_ready_o;
            st1_req_is_error_o = st0_req_is_error_i;

            //      New cacheable stage 0 request granted
            //      {{{
            //          IMPORTANT: here the RAM is enabled independently if the
            //          request needs to be put on-hold.
            //          This increases the power consumption in that cases, but
            //          removes the timing paths RAM-to-RAM between the cache
            //          directory and the data array.
            if ((core_req_ready_o | rtab_req_ready_o) &&
                !st0_req_is_uncacheable_i &&
                !st0_req_is_error_i)
            begin
                st1_req_is_cacheable_store = st1_req_valid_i & st1_req_is_store_i &
                        ~st1_req_is_uncacheable_i;

                st0_req_cachedata_read_o = st0_req_is_load_i &
                        (~st1_req_is_cacheable_store | st1_req_is_error_i);

                if (st0_req_is_load_i         |
                    st0_req_is_cmo_prefetch_i |
                    st0_req_is_store_i        |
                    st0_req_is_amo_i          )
                begin
                    st0_req_mshr_check_o    = 1'b1;
                    st0_req_cachedir_read_o = 1'b1;
                end
            end
            //      }}}
            //  }}}
        end
        //  }}} end of normal pipeline operation
    end
    //  }}}
endmodule
