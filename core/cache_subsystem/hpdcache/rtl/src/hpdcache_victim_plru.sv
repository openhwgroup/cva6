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
 *  Creation Date : May, 2021
 *  Description   : HPDcache Pseudo-LRU replacement policy
 *  History       :
 */
module hpdcache_victim_plru
import hpdcache_pkg::*;
    //  Parameters
    //  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    localparam type set_t        = logic [$clog2(HPDcacheCfg.u.sets)-1:0],
    localparam type way_vector_t = logic [HPDcacheCfg.u.ways-1:0]
)
    //  }}}

    //  Ports
    //  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,

    //      PLRU update interface
    input  logic                  updt_i,
    input  set_t                  updt_set_i,
    input  way_vector_t           updt_way_i,

    //      Victim selection interface
    input  logic                  sel_victim_i, /* unused */
    input  way_vector_t           sel_dir_valid_i,
    input  way_vector_t           sel_dir_wback_i,
    input  way_vector_t           sel_dir_dirty_i,
    input  way_vector_t           sel_dir_fetch_i,
    input  set_t                  sel_victim_set_i,
    output way_vector_t           sel_victim_way_o
);
    //  }}}

    //  Internal signals and registers
    //  {{{
    way_vector_t [HPDcacheCfg.u.sets-1:0] plru_q, plru_d;

    way_vector_t updt_plru;
    logic        unused_available, plru_available, clean_available, dirty_available;
    way_vector_t unused_ways, plru_ways, clean_ways, dirty_ways;
    way_vector_t unused_victim_way, plru_victim_way, clean_victim_way, dirty_victim_way;
    //  }}}

    //  Victim way selection
    //  {{{
    assign unused_ways = ~sel_dir_fetch_i & ~sel_dir_valid_i;
    assign plru_ways   = ~sel_dir_fetch_i &  sel_dir_valid_i & ~plru_q[sel_victim_set_i];
    assign clean_ways  = ~sel_dir_fetch_i &  sel_dir_valid_i & ~sel_dir_dirty_i;
    assign dirty_ways  = ~sel_dir_fetch_i &  sel_dir_valid_i &  sel_dir_dirty_i;

    hpdcache_prio_1hot_encoder #(.N(HPDcacheCfg.u.ways))
        unused_victim_select_i(
            .val_i     (unused_ways),
            .val_o     (unused_victim_way)
        );

    hpdcache_prio_1hot_encoder #(.N(HPDcacheCfg.u.ways))
        plru_victim_select_i(
            .val_i     (plru_ways),
            .val_o     (plru_victim_way)
        );

    hpdcache_prio_1hot_encoder #(.N(HPDcacheCfg.u.ways))
        clean_victim_select_i(
            .val_i     (clean_ways),
            .val_o     (clean_victim_way)
        );

    hpdcache_prio_1hot_encoder #(.N(HPDcacheCfg.u.ways))
        dirty_victim_select_i(
            .val_i     (dirty_ways),
            .val_o     (dirty_victim_way)
        );

    assign unused_available = |unused_ways;
    assign plru_available   = |plru_ways;
    assign clean_available  = |clean_ways;
    assign dirty_available  = |dirty_ways;

    always_comb
    begin : victim_way_selection_comb
        priority case (1'b1)
            unused_available: sel_victim_way_o = unused_victim_way;
            plru_available:   sel_victim_way_o = plru_victim_way;
            clean_available:  sel_victim_way_o = clean_victim_way;
            dirty_available:  sel_victim_way_o = dirty_victim_way;
            default:          sel_victim_way_o = '0;
        endcase
    end
    //  }}}

    //  Pseudo-LRU update process
    //  {{{
    assign updt_plru = plru_q[updt_set_i] | updt_way_i;

    always_comb
    begin : plru_update_comb
        plru_d = plru_q;

        //  When accessing a cache-line, set the corresponding PLRU bit
        //  If all PLRU bits of a given set are equal to 1, reset them all
        //  but the currently accessed way
        if (updt_i) plru_d[updt_set_i] = &updt_plru ? updt_way_i : updt_plru;
    end
    //  }}}

    //  Set state process
    //  {{{
    always_ff @(posedge clk_i or negedge rst_ni)
    begin : lru_ff
        if (!rst_ni) begin
           plru_q <= '0;
        end else begin
           if (updt_i) plru_q <= plru_d;
        end
    end
    //  }}}

endmodule
