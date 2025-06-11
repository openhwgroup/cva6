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
 *  Description   : Dcache memory request to axi read channels
 *  History       :
 */
module hpdcache_mem_to_axi_read
import hpdcache_pkg::*;
#(
    parameter type hpdcache_mem_req_t    = logic,
    parameter type hpdcache_mem_resp_r_t = logic,
    parameter type ar_chan_t = logic,
    parameter type r_chan_t  = logic
)
(
    output logic                          req_ready_o,
    input  logic                          req_valid_i,
    input  hpdcache_mem_req_t             req_i,

    input  logic                          resp_ready_i,
    output logic                          resp_valid_o,
    output hpdcache_mem_resp_r_t          resp_o,

    output logic                          axi_ar_valid_o,
    output ar_chan_t                      axi_ar_o,
    input  logic                          axi_ar_ready_i,

    input  logic                          axi_r_valid_i,
    input  r_chan_t                       axi_r_i,
    output logic                          axi_r_ready_o
);

    logic                lock;
    axi_pkg::cache_t     cache;
    hpdcache_mem_error_e resp;

    assign  lock  = (req_i.mem_req_command == HPDCACHE_MEM_ATOMIC) &&
                    (req_i.mem_req_atomic  == HPDCACHE_MEM_ATOMIC_LDEX);

    assign  cache = req_i.mem_req_cacheable ?
                    axi_pkg::CACHE_BUFFERABLE |
                    axi_pkg::CACHE_MODIFIABLE |
                    axi_pkg::CACHE_RD_ALLOC   |
                    axi_pkg::CACHE_WR_ALLOC   : axi_pkg::CACHE_MODIFIABLE;

    always_comb
    begin : resp_decode_comb
        case (axi_r_i.resp)
            axi_pkg::RESP_SLVERR,
            axi_pkg::RESP_DECERR: resp = HPDCACHE_MEM_RESP_NOK;
            default:              resp = HPDCACHE_MEM_RESP_OK;
        endcase
    end

    assign  req_ready_o       = axi_ar_ready_i,
            axi_ar_valid_o    = req_valid_i,
            axi_ar_o.id       = req_i.mem_req_id,
            axi_ar_o.addr     = req_i.mem_req_addr,
            axi_ar_o.len      = req_i.mem_req_len,
            axi_ar_o.size     = req_i.mem_req_size,
            axi_ar_o.burst    = axi_pkg::BURST_INCR,
            axi_ar_o.lock     = lock,
            axi_ar_o.cache    = cache,
            axi_ar_o.prot     = '0,
            axi_ar_o.qos      = '0,
            axi_ar_o.region   = '0,
            axi_ar_o.user     = '0;

    assign  axi_r_ready_o           = resp_ready_i,
            resp_valid_o            = axi_r_valid_i,
            resp_o.mem_resp_r_error = resp,
            resp_o.mem_resp_r_id    = axi_r_i.id,
            resp_o.mem_resp_r_data  = axi_r_i.data,
            resp_o.mem_resp_r_last  = axi_r_i.last;

endmodule
