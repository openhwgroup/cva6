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
 *  Description   : HPDcache Miss Status Holding Register (MSHR)
 *  History       :
 */
module hpdcache_mshr
import hpdcache_pkg::*;
    //  Parameters
    //  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,
    parameter type hpdcache_nline_t = logic,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_set_t = logic,
    parameter type hpdcache_word_t = logic,
    parameter type hpdcache_way_t = logic,

    parameter type hpdcache_req_tid_t = logic,
    parameter type hpdcache_req_sid_t = logic,

    parameter type mshr_way_t = logic,
    parameter type mshr_set_t = logic
)
    //  }}}

    //  Ports
    //  {{{
(
    //  Clock and reset signals
    input  logic                  clk_i,
    input  logic                  rst_ni,

    //  Global control signals
    output logic                  empty_o,
    output logic                  full_o,

    //  Check and allocation interface
    input  logic                  check_i,
    input  hpdcache_set_t         check_set_i,
    input  hpdcache_tag_t         check_tag_i,
    output logic                  hit_o,
    input  logic                  alloc_i,
    input  logic                  alloc_cs_i,
    input  hpdcache_nline_t       alloc_nline_i,
    input  hpdcache_req_tid_t     alloc_req_id_i,
    input  hpdcache_req_sid_t     alloc_src_id_i,
    input  hpdcache_word_t        alloc_word_i,
    input  hpdcache_way_t         alloc_victim_way_i,
    input  logic                  alloc_need_rsp_i,
    input  logic                  alloc_is_prefetch_i,
    input  logic                  alloc_wback_i,
    output logic                  alloc_full_o,
    output mshr_way_t             alloc_way_o,

    //  Acknowledge interface
    input  logic                  ack_i,
    input  logic                  ack_cs_i,
    input  mshr_set_t             ack_set_i,
    input  mshr_way_t             ack_way_i,
    output hpdcache_req_tid_t     ack_req_id_o,
    output hpdcache_req_sid_t     ack_src_id_o,
    output hpdcache_set_t         ack_cache_set_o,
    output hpdcache_way_t         ack_cache_way_o,
    output hpdcache_tag_t         ack_cache_tag_o,
    output hpdcache_word_t        ack_word_o,
    output logic                  ack_need_rsp_o,
    output logic                  ack_is_prefetch_o,
    output logic                  ack_wback_o
);
    //  }}}

    //  Definition of constants and types
    //  {{{
    typedef struct packed {
        hpdcache_tag_t     tag;
        hpdcache_req_tid_t req_id;
        hpdcache_req_sid_t src_id;
        hpdcache_word_t    word_idx;
        hpdcache_way_t     victim_way_idx;
        logic              wback;
        logic              need_rsp;
        logic              is_prefetch;
    } mshr_entry_t;


    //  Compute the width of MSHR entries depending on the support of write
    //  bitmask or not (write byte enable)
    localparam int unsigned HPDCACHE_MSHR_ENTRY_BITS = $bits(mshr_entry_t);

    localparam int unsigned HPDCACHE_MSHR_RAM_ENTRY_BITS =
            HPDcacheCfg.u.mshrRamByteEnable ?
                    ((HPDCACHE_MSHR_ENTRY_BITS + 7)/8) * 8 : // align to 8 bits
                      HPDCACHE_MSHR_ENTRY_BITS;              // or use the exact number of bits

    typedef logic [HPDCACHE_MSHR_RAM_ENTRY_BITS-1:0] mshr_sram_data_t;
    //  }}}

    //  Definition of internal wires and registers
    //  {{{
    logic          [HPDcacheCfg.u.mshrSets*HPDcacheCfg.u.mshrWays-1:0] mshr_valid_q;
    hpdcache_set_t [HPDcacheCfg.u.mshrSets*HPDcacheCfg.u.mshrWays-1:0] mshr_cache_set_q;

    hpdcache_set_t check_cache_set_q;
    mshr_set_t     check_set_st0, check_set_st1;
    mshr_set_t     alloc_set;
    mshr_way_t     ack_way_q;

    logic [HPDcacheCfg.u.mshrSets*HPDcacheCfg.u.mshrWays-1:0] mshr_valid_set, mshr_valid_rst;
    mshr_entry_t     [HPDcacheCfg.u.mshrWays-1:0] mshr_wentry;
    mshr_sram_data_t [HPDcacheCfg.u.mshrWays-1:0] mshr_wdata;
    mshr_entry_t     [HPDcacheCfg.u.mshrWays-1:0] mshr_rentry;
    mshr_sram_data_t [HPDcacheCfg.u.mshrWays-1:0] mshr_rdata;

    logic mshr_we;
    logic mshr_cs;
    mshr_set_t  mshr_addr;
    logic check;
    //  }}}

    //  Control part for the allocation and check operations
    //  {{{

    //    The allocation operation is prioritary with respect to the check operation
    assign check = check_i & ~alloc_i;

    if (HPDcacheCfg.u.mshrSets > 1) begin : gen_alloc_mshr_sets_gt_1
      assign check_set_st0 = check_set_i[0 +: HPDcacheCfg.mshrSetWidth];
      assign check_set_st1 = check_cache_set_q[0 +: HPDcacheCfg.mshrSetWidth];
      assign alloc_set = alloc_nline_i[0 +: HPDcacheCfg.mshrSetWidth];
    end else begin : gen_alloc_mshr_sets_eq_1
      assign check_set_st0 = '0;
      assign check_set_st1 = '0;
      assign alloc_set = '0;
    end

    //    Look for an available way in case of allocation
    always_comb
    begin
        automatic mshr_way_t found_available_way;

        found_available_way = 0;
        for (int unsigned i = 0; i < HPDcacheCfg.u.mshrWays; i++) begin
            if (!mshr_valid_q[i*HPDcacheCfg.u.mshrSets + hpdcache_uint32'(alloc_set)]) begin
                found_available_way = mshr_way_t'(i);
                break;
            end
        end
        alloc_way_o = found_available_way;
    end

    //    Look if the mshr can accept the checked nline (in case of allocation)
    always_comb
    begin
        automatic bit found_available;

        found_available = 1'b0;
        for (int unsigned i = 0; i < HPDcacheCfg.u.mshrWays; i++) begin
            if (!mshr_valid_q[i*HPDcacheCfg.u.mshrSets + hpdcache_uint32'(check_set_st1)]) begin
                found_available = 1'b1;
                break;
            end
        end
        alloc_full_o = ~found_available;
    end

    //    Write when there is an allocation operation
    assign mshr_we = alloc_i;

    //    Generate write data and mask depending on the available way
    always_comb
    begin
        for (int unsigned i = 0; i < HPDcacheCfg.u.mshrWays; i++) begin
            mshr_wentry[i].tag = alloc_nline_i[HPDcacheCfg.setWidth +: HPDcacheCfg.tagWidth];
            mshr_wentry[i].req_id = alloc_req_id_i;
            mshr_wentry[i].src_id = alloc_src_id_i;
            mshr_wentry[i].word_idx = alloc_word_i;
            mshr_wentry[i].victim_way_idx = alloc_victim_way_i;
            mshr_wentry[i].need_rsp = alloc_need_rsp_i;
            mshr_wentry[i].is_prefetch = alloc_is_prefetch_i;
            mshr_wentry[i].wback = alloc_wback_i;
        end
    end
    //  }}}

    //  Shared control signals
    //  {{{
    hpdcache_uint mshr_alloc_slot;
    hpdcache_uint mshr_ack_slot;

    if ((HPDcacheCfg.u.mshrSets > 1) && (HPDcacheCfg.u.mshrWays > 1))
    begin : gen_mshr_set_associative
        assign mshr_alloc_slot = hpdcache_uint'({alloc_way_o, alloc_set});
        assign mshr_ack_slot   = hpdcache_uint'({  ack_way_i, ack_set_i});
    end else if (HPDcacheCfg.u.mshrSets > 1) begin : gen_mshr_direct_mapped
        assign mshr_alloc_slot = hpdcache_uint'(alloc_set);
        assign mshr_ack_slot   = hpdcache_uint'(ack_set_i);
    end else if (HPDcacheCfg.u.mshrWays > 1) begin : gen_mshr_fully_associative
        assign mshr_alloc_slot = hpdcache_uint'(alloc_way_o);
        assign mshr_ack_slot   = hpdcache_uint'(ack_way_i);
    end else begin : gen_mshr_single_entry
        assign mshr_alloc_slot = '0;
        assign mshr_ack_slot   = '0;
    end

    assign mshr_cs   = check_i | alloc_cs_i | ack_cs_i;
    assign mshr_addr = ack_i ? ack_set_i : (alloc_i ? alloc_set : check_set_st0);

    always_comb
    begin : mshr_valid_comb
        for (hpdcache_uint i = 0; i < HPDcacheCfg.u.mshrSets*HPDcacheCfg.u.mshrWays; i++) begin
            mshr_valid_rst[i] = (i ==   mshr_ack_slot) ? ack_i   : 1'b0;
            mshr_valid_set[i] = (i == mshr_alloc_slot) ? alloc_i : 1'b0;
        end
    end
    //  }}}

    //  Read interface (ack)
    //  {{{
    assign ack_cache_set_o   = mshr_cache_set_q[mshr_ack_slot];
    assign ack_cache_way_o   = mshr_rentry[ack_way_q].victim_way_idx;
    assign ack_cache_tag_o   = mshr_rentry[ack_way_q].tag;
    assign ack_req_id_o      = mshr_rentry[ack_way_q].req_id;
    assign ack_src_id_o      = mshr_rentry[ack_way_q].src_id;
    assign ack_word_o        = mshr_rentry[ack_way_q].word_idx;
    assign ack_need_rsp_o    = mshr_rentry[ack_way_q].need_rsp;
    assign ack_is_prefetch_o = mshr_rentry[ack_way_q].is_prefetch;
    assign ack_wback_o       = mshr_rentry[ack_way_q].wback;
    //  }}}

    //  Global control signals
    //  {{{
    assign empty_o  = ~|mshr_valid_q;
    assign full_o   =  &mshr_valid_q;

    always_comb
    begin : hit_comb
        automatic bit [HPDcacheCfg.u.mshrWays-1:0] v_hit_way;

        for (int unsigned w = 0; w < HPDcacheCfg.u.mshrWays; w++) begin
            automatic bit v_valid;
            hpdcache_uint32 v_check_set_st1;
            hpdcache_set_t v_check_set;
            automatic bit v_match_set;
            automatic bit v_match_tag;

            v_valid = mshr_valid_q[w*HPDcacheCfg.u.mshrSets + hpdcache_uint32'(check_set_st1)];
            v_check_set_st1 = hpdcache_uint32'(check_set_st1);
            v_check_set = mshr_cache_set_q[w*HPDcacheCfg.u.mshrSets + v_check_set_st1];
            v_match_set = (v_check_set == check_cache_set_q);
            v_match_tag = (mshr_rentry[w].tag == check_tag_i);
            v_hit_way[w] = (v_valid && v_match_tag && v_match_set);
        end

        hit_o = |v_hit_way;
    end
    //  }}}

    //  Internal state assignment
    //  {{{
    always_ff @(posedge clk_i or negedge rst_ni)
    begin : mshr_ff_set
        if (!rst_ni) begin
            mshr_valid_q <= '0;
            ack_way_q <= '0;
            check_cache_set_q <= '0;
        end else begin
            mshr_valid_q <= (~mshr_valid_q & mshr_valid_set) | (mshr_valid_q & ~mshr_valid_rst);
            if (ack_i) ack_way_q <= ack_way_i;
            if (check) check_cache_set_q <= check_set_i;
        end
    end
    //  }}}

    //  Internal components
    //  {{{
    typedef logic [HPDCACHE_MSHR_RAM_ENTRY_BITS/8-1:0] mshr_sram_wbyteenable_t;
    typedef logic [HPDCACHE_MSHR_RAM_ENTRY_BITS-1:0] mshr_sram_wmask_t;
    if (HPDcacheCfg.u.mshrRamByteEnable) begin : gen_mshr_wbyteenable
        mshr_sram_wbyteenable_t [HPDcacheCfg.u.mshrWays-1:0] mshr_wbyteenable;

        always_comb
        begin : mshr_wbyteenable_comb
            for (int unsigned i = 0; i < HPDcacheCfg.u.mshrWays; i++) begin
                mshr_wbyteenable[i] = (hpdcache_uint32'(alloc_way_o) == i) ? '1 : '0;
            end
        end

        if (HPDcacheCfg.u.mshrUseRegbank) begin : gen_mshr_regbank
            hpdcache_regbank_wbyteenable_1rw #(
                .DATA_SIZE     (HPDcacheCfg.u.mshrWays*HPDCACHE_MSHR_RAM_ENTRY_BITS),
                .ADDR_SIZE     (HPDcacheCfg.mshrSetWidth),
                .DEPTH         (HPDcacheCfg.u.mshrSets)
            ) mshr_mem(
                .clk           (clk_i),
                .rst_n         (rst_ni),
                .cs            (mshr_cs),
                .we            (mshr_we),
                .addr          (mshr_addr),
                .wbyteenable   (mshr_wbyteenable),
                .wdata         (mshr_wdata),
                .rdata         (mshr_rdata)
            );
        end else begin : gen_mshr_sram
            hpdcache_sram_wbyteenable #(
                .DATA_SIZE     (HPDcacheCfg.u.mshrWays*HPDCACHE_MSHR_RAM_ENTRY_BITS),
                .ADDR_SIZE     (HPDcacheCfg.mshrSetWidth),
                .DEPTH         (HPDcacheCfg.u.mshrSets)
            ) mshr_mem(
                .clk           (clk_i),
                .rst_n         (rst_ni),
                .cs            (mshr_cs),
                .we            (mshr_we),
                .addr          (mshr_addr),
                .wbyteenable   (mshr_wbyteenable),
                .wdata         (mshr_wdata),
                .rdata         (mshr_rdata)
            );
        end
    end else begin : gen_mshr_wmask
        mshr_sram_wmask_t [HPDcacheCfg.u.mshrWays-1:0] mshr_wmask;

        always_comb
        begin : mshr_wmask_comb
            for (int unsigned i = 0; i < HPDcacheCfg.u.mshrWays; i++) begin
                mshr_wmask[i] = (hpdcache_uint32'(alloc_way_o) == i) ? '1 : '0;
            end
        end

        if (HPDcacheCfg.u.mshrUseRegbank) begin : gen_mshr_regbank
            hpdcache_regbank_wmask_1rw #(
                .DATA_SIZE     (HPDcacheCfg.u.mshrWays*HPDCACHE_MSHR_RAM_ENTRY_BITS),
                .ADDR_SIZE     (HPDcacheCfg.mshrSetWidth),
                .DEPTH         (HPDcacheCfg.u.mshrSets)
            ) mshr_mem(
                .clk           (clk_i),
                .rst_n         (rst_ni),
                .cs            (mshr_cs),
                .we            (mshr_we),
                .addr          (mshr_addr),
                .wmask         (mshr_wmask),
                .wdata         (mshr_wdata),
                .rdata         (mshr_rdata)
            );
        end else begin : gen_mshr_sram
            hpdcache_sram_wmask #(
                .DATA_SIZE     (HPDcacheCfg.u.mshrWays*HPDCACHE_MSHR_RAM_ENTRY_BITS),
                .ADDR_SIZE     (HPDcacheCfg.mshrSetWidth),
                .DEPTH         (HPDcacheCfg.u.mshrSets)
            ) mshr_mem(
                .clk           (clk_i),
                .rst_n         (rst_ni),
                .cs            (mshr_cs),
                .we            (mshr_we),
                .addr          (mshr_addr),
                .wmask         (mshr_wmask),
                .wdata         (mshr_wdata),
                .rdata         (mshr_rdata)
            );
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni)
    begin
        if (!rst_ni) begin
          mshr_cache_set_q <= '0;
        end else begin
            if (alloc_i) begin
                mshr_cache_set_q[mshr_alloc_slot] <= alloc_nline_i[0 +: HPDcacheCfg.setWidth];
            end
        end
    end

    always_comb
    begin : ram_word_fitting_comb
        for (int unsigned i = 0; i < HPDcacheCfg.u.mshrWays; i++) begin
            mshr_wdata[i]  = mshr_sram_data_t'(mshr_wentry[i]);
            mshr_rentry[i] = mshr_entry_t'(mshr_rdata[i][0 +: HPDCACHE_MSHR_ENTRY_BITS]);
        end
    end
    //  }}}

    //  Assertions
    //  {{{
`ifndef HPDCACHE_ASSERT_OFF
    one_command_assert: assert property (@(posedge clk_i)
            (ack_i -> !(alloc_i || check_i))) else
            $error("MSHR: ack with concurrent alloc or check");
`endif
    //  }}}
endmodule
