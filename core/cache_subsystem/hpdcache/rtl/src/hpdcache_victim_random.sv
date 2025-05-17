/*
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
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : September, 2024
 *  Description   : HPDcache pseudo-random replacement policy
 *  History       :
 */
module hpdcache_victim_random
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

    //      Update interface
    input  logic                  updt_i, /* unused */
    input  set_t                  updt_set_i, /* unused */
    input  way_vector_t           updt_way_i, /* unused */

    //      Victim selection interface
    input  logic                  sel_victim_i,
    input  way_vector_t           sel_dir_valid_i,
    input  way_vector_t           sel_dir_wback_i, /* unused */
    input  way_vector_t           sel_dir_dirty_i,
    input  way_vector_t           sel_dir_fetch_i,
    input  set_t                  sel_victim_set_i, /* unused */
    output way_vector_t           sel_victim_way_o
);
    //  }}}

    //  Internal signals and registers
    //  {{{
    logic         unused_available, rand_available, clean_available, dirty_available;
    way_vector_t  unused_ways, rand_ways, clean_ways, dirty_ways;
    way_vector_t  unused_victim_way, rand_victim_way, clean_victim_way, dirty_victim_way;
    logic [7:0]   lfsr_val;
    //  }}}

    //  Victim way selection
    //  {{{
    assign unused_ways = ~sel_dir_fetch_i & ~sel_dir_valid_i;
    assign rand_ways   = ~sel_dir_fetch_i &  sel_dir_valid_i &  rand_victim_way;
    assign clean_ways  = ~sel_dir_fetch_i &  sel_dir_valid_i & ~sel_dir_dirty_i;
    assign dirty_ways  = ~sel_dir_fetch_i &  sel_dir_valid_i &  sel_dir_dirty_i;

    hpdcache_lfsr #(.WIDTH(8))
        lfsr_i(
            .clk_i,
            .rst_ni,
            .shift_i   (sel_victim_i & ~unused_available & rand_available),
            .val_o     (lfsr_val)
        );

    hpdcache_decoder #(.N(HPDcacheCfg.wayIndexWidth))
        rand_way_decoder_i(
            .en_i      (1'b1),
            .val_i     (lfsr_val[0 +: HPDcacheCfg.wayIndexWidth]),
            .val_o     (rand_victim_way)
        );

    hpdcache_prio_1hot_encoder #(.N(HPDcacheCfg.u.ways))
        unused_victim_select_i(
            .val_i     (unused_ways),
            .val_o     (unused_victim_way)
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
    assign rand_available   = |rand_ways;
    assign clean_available  = |clean_ways;
    assign dirty_available  = |dirty_ways;

    always_comb
    begin : victim_way_selection_comb
        priority case (1'b1)
            unused_available: sel_victim_way_o = unused_victim_way;
            rand_available:   sel_victim_way_o = rand_victim_way;
            clean_available:  sel_victim_way_o = clean_victim_way;
            dirty_available:  sel_victim_way_o = dirty_victim_way;
            default:          sel_victim_way_o = '0;
        endcase
    end
    //  }}}

endmodule
