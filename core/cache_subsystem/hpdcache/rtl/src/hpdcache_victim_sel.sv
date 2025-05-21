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
 *  Creation Date : Mars, 2024
 *  Description   : HPDcache Victim Selection
 *  History       :
 */
module hpdcache_victim_sel
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    parameter type hpdcache_set_t = logic,
    parameter type hpdcache_way_vector_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,

    //      Victim policy update interface
    input  logic                  updt_i,
    input  hpdcache_set_t         updt_set_i,
    input  hpdcache_way_vector_t  updt_way_i,

    //      Victim selection interface
    input  logic                  sel_victim_i,
    input  hpdcache_way_vector_t  sel_dir_valid_i,
    input  hpdcache_way_vector_t  sel_dir_wback_i,
    input  hpdcache_way_vector_t  sel_dir_dirty_i,
    input  hpdcache_way_vector_t  sel_dir_fetch_i,
    input  hpdcache_set_t         sel_victim_set_i,
    output hpdcache_way_vector_t  sel_victim_way_o
);
//  }}}

    //  -----------------------------------------------------------------------
    //  Direct mapped cache (one way)
    if (HPDcacheCfg.u.ways == 1)
    begin : gen_single_way_victim_sel
        assign sel_victim_way_o = 1'b1;
    end

    //  -----------------------------------------------------------------------
    //  Set-associative cache with pseudo random victim selection
    else if (HPDcacheCfg.u.victimSel == HPDCACHE_VICTIM_RANDOM)
    begin : gen_random_victim_sel
        hpdcache_victim_random #(
            .HPDcacheCfg (HPDcacheCfg)
        ) victim_rand_i(
            .clk_i,
            .rst_ni,

            .updt_i,
            .updt_set_i,
            .updt_way_i,

            .sel_victim_i,
            .sel_dir_valid_i,
            .sel_dir_wback_i,
            .sel_dir_dirty_i,
            .sel_dir_fetch_i,
            .sel_victim_set_i,
            .sel_victim_way_o
        );
    end

    //  -----------------------------------------------------------------------
    //  Set-associative cache with pseudo least-recently-used victim selection
    else if (HPDcacheCfg.u.victimSel == HPDCACHE_VICTIM_PLRU)
    begin : gen_plru_victim_sel
        hpdcache_victim_plru #(
            .HPDcacheCfg (HPDcacheCfg)
        ) victim_plru_i(
            .clk_i,
            .rst_ni,

            .updt_i,
            .updt_set_i,
            .updt_way_i,

            .sel_victim_i,
            .sel_dir_valid_i,
            .sel_dir_wback_i,
            .sel_dir_dirty_i,
            .sel_dir_fetch_i,
            .sel_victim_set_i,
            .sel_victim_way_o
        );
    end

`ifndef HPDCACHE_ASSERT_OFF
    initial victim_sel_assert:
            assert (HPDcacheCfg.u.victimSel inside {HPDCACHE_VICTIM_RANDOM, HPDCACHE_VICTIM_PLRU})
                    else $fatal("unsupported victim selection policy");
`endif

endmodule
