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
 *  Description   : Dcache memory request to axi write channels
 *  History       :
 */
module hpdcache_mem_to_axi_write
import hpdcache_pkg::*;
#(
    parameter type hpdcache_mem_req_t = logic,
    parameter type hpdcache_mem_req_w_t = logic,
    parameter type hpdcache_mem_resp_w_t = logic,
    parameter type aw_chan_t = logic,
    parameter type w_chan_t = logic,
    parameter type b_chan_t = logic
)
(
    output logic                          req_ready_o,
    input  logic                          req_valid_i,
    input  hpdcache_mem_req_t             req_i,

    output logic                          req_data_ready_o,
    input  logic                          req_data_valid_i,
    input  hpdcache_mem_req_w_t           req_data_i,

    input  logic                          resp_ready_i,
    output logic                          resp_valid_o,
    output hpdcache_mem_resp_w_t          resp_o,

    output logic                          axi_aw_valid_o,
    output aw_chan_t                      axi_aw_o,
    input  logic                          axi_aw_ready_i,

    output logic                          axi_w_valid_o,
    output w_chan_t                       axi_w_o,
    input  logic                          axi_w_ready_i,

    input  logic                          axi_b_valid_i,
    input  b_chan_t                       axi_b_i,
    output logic                          axi_b_ready_o
);

    logic                lock;
    axi_pkg::atop_t      atop;
    axi_pkg::cache_t     cache;
    hpdcache_mem_error_e resp;

    always_comb
    begin : atop_comb
        lock = 1'b0;
        atop = '0;
        case (req_i.mem_req_command)
            HPDCACHE_MEM_ATOMIC: begin
                case (req_i.mem_req_atomic)
                    HPDCACHE_MEM_ATOMIC_STEX: lock = 1'b1;
                    HPDCACHE_MEM_ATOMIC_ADD : atop = {axi_pkg::ATOP_ATOMICLOAD,
                                                      axi_pkg::ATOP_LITTLE_END,
                                                      axi_pkg::ATOP_ADD};
                    HPDCACHE_MEM_ATOMIC_CLR : atop = {axi_pkg::ATOP_ATOMICLOAD,
                                                      axi_pkg::ATOP_LITTLE_END,
                                                      axi_pkg::ATOP_CLR};
                    HPDCACHE_MEM_ATOMIC_SET : atop = {axi_pkg::ATOP_ATOMICLOAD,
                                                      axi_pkg::ATOP_LITTLE_END,
                                                      axi_pkg::ATOP_SET};
                    HPDCACHE_MEM_ATOMIC_EOR : atop = {axi_pkg::ATOP_ATOMICLOAD,
                                                      axi_pkg::ATOP_LITTLE_END,
                                                      axi_pkg::ATOP_EOR};
                    HPDCACHE_MEM_ATOMIC_SMAX: atop = {axi_pkg::ATOP_ATOMICLOAD,
                                                      axi_pkg::ATOP_LITTLE_END,
                                                      axi_pkg::ATOP_SMAX};
                    HPDCACHE_MEM_ATOMIC_SMIN: atop = {axi_pkg::ATOP_ATOMICLOAD,
                                                      axi_pkg::ATOP_LITTLE_END,
                                                      axi_pkg::ATOP_SMIN};
                    HPDCACHE_MEM_ATOMIC_UMAX: atop = {axi_pkg::ATOP_ATOMICLOAD,
                                                      axi_pkg::ATOP_LITTLE_END,
                                                      axi_pkg::ATOP_UMAX};
                    HPDCACHE_MEM_ATOMIC_UMIN: atop = {axi_pkg::ATOP_ATOMICLOAD,
                                                      axi_pkg::ATOP_LITTLE_END,
                                                      axi_pkg::ATOP_UMIN};
                    HPDCACHE_MEM_ATOMIC_SWAP: atop =  axi_pkg::ATOP_ATOMICSWAP;
                endcase
            end
        endcase
    end

    assign  cache = (req_i.mem_req_cacheable && !lock) ?
                        axi_pkg::CACHE_BUFFERABLE |
                        axi_pkg::CACHE_MODIFIABLE |
                        axi_pkg::CACHE_RD_ALLOC   |
                        axi_pkg::CACHE_WR_ALLOC   : axi_pkg::CACHE_MODIFIABLE;

    always_comb
    begin : resp_decode_comb
        case (axi_b_i.resp)
            axi_pkg::RESP_SLVERR,
            axi_pkg::RESP_DECERR: resp = HPDCACHE_MEM_RESP_NOK;
            default:              resp = HPDCACHE_MEM_RESP_OK;
        endcase
    end

    assign  req_ready_o                     = axi_aw_ready_i,
            axi_aw_valid_o                  = req_valid_i,
            axi_aw_o.id                     = req_i.mem_req_id,
            axi_aw_o.addr                   = req_i.mem_req_addr,
            axi_aw_o.len                    = req_i.mem_req_len,
            axi_aw_o.size                   = req_i.mem_req_size,
            axi_aw_o.burst                  = axi_pkg::BURST_INCR,
            axi_aw_o.lock                   = lock,
            axi_aw_o.cache                  = cache,
            axi_aw_o.prot                   = '0,
            axi_aw_o.qos                    = '0,
            axi_aw_o.region                 = '0,
            axi_aw_o.atop                   = atop,
            axi_aw_o.user                   = '0;

    assign  req_data_ready_o                = axi_w_ready_i,
            axi_w_valid_o                   = req_data_valid_i,
            axi_w_o.data                    = req_data_i.mem_req_w_data,
            axi_w_o.strb                    = req_data_i.mem_req_w_be,
            axi_w_o.last                    = req_data_i.mem_req_w_last,
            axi_w_o.user                    = '0;

    assign  axi_b_ready_o                   = resp_ready_i,
            resp_valid_o                    = axi_b_valid_i,
            resp_o.mem_resp_w_error         = resp,
            resp_o.mem_resp_w_id            = axi_b_i.id,
            resp_o.mem_resp_w_is_atomic     = (axi_b_i.resp == axi_pkg::RESP_EXOKAY);

endmodule
