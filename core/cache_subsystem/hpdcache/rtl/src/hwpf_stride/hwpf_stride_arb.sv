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
 *  Author(s)     : Riccardo Alidori, Cesar Fuguet
 *  Creation Date : June, 2021
 *  Description   : Hw prefetchers arbiter
 *  History       :
 */
module hwpf_stride_arb
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter int NUM_HW_PREFETCH = 4,

    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input  logic                                clk_i,
    input  logic                                rst_ni,

    // Dcache input interface
    input  logic          [NUM_HW_PREFETCH-1:0] hwpf_stride_req_valid_i,
    output logic          [NUM_HW_PREFETCH-1:0] hwpf_stride_req_ready_o,
    input  hpdcache_req_t [NUM_HW_PREFETCH-1:0] hwpf_stride_req_i,
    output logic          [NUM_HW_PREFETCH-1:0] hwpf_stride_rsp_valid_o,
    output hpdcache_rsp_t [NUM_HW_PREFETCH-1:0] hwpf_stride_rsp_o,       // Not used

    // Dcache output interface
    output logic                                hpdcache_req_valid_o,
    input  logic                                hpdcache_req_ready_i,
    output hpdcache_req_t                       hpdcache_req_o,
    input  logic                                hpdcache_rsp_valid_i,
    input  hpdcache_rsp_t                       hpdcache_rsp_i           // Not used
);
//  }}}

    //  Internal signals
    //  {{{
    logic          [NUM_HW_PREFETCH-1:0] hwpf_stride_req_valid;
    hpdcache_req_t [NUM_HW_PREFETCH-1:0] hwpf_stride_req;
    logic          [NUM_HW_PREFETCH-1:0] arb_req_gnt;
    //  }}}

    //  Requesters arbiter
    //  {{{
    //      Pack request ports
    genvar gen_i;
    generate
        for (gen_i = 0; gen_i < NUM_HW_PREFETCH; gen_i++) begin : gen_hwpf_stride_req
            assign hwpf_stride_req_ready_o[gen_i] = arb_req_gnt[gen_i] & hpdcache_req_ready_i,
                   hwpf_stride_req_valid[gen_i]   = hwpf_stride_req_valid_i[gen_i],
                   hwpf_stride_req[gen_i]         = hwpf_stride_req_i[gen_i];
        end
    endgenerate

    //      Arbiter
    hpdcache_rrarb #(
        .N              (NUM_HW_PREFETCH)
    ) hwpf_stride_req_arbiter_i (
        .clk_i,
        .rst_ni,
        .req_i          (hwpf_stride_req_valid),
        .gnt_o          (arb_req_gnt),
        .ready_i        (hpdcache_req_ready_i)
    );

    //      Request Multiplexor
    hpdcache_mux #(
        .NINPUT         (NUM_HW_PREFETCH),
        .DATA_WIDTH     ($bits(hpdcache_req_t)),
        .ONE_HOT_SEL    (1'b1)
    ) hwpf_stride_req_mux_i (
        .data_i         (hwpf_stride_req),
        .sel_i          (arb_req_gnt),
        .data_o         (hpdcache_req_o)
    );

    assign hpdcache_req_valid_o = |arb_req_gnt;
    //  }}}

    //  Response demultiplexor
    //  {{{
    //      As the HW prefetcher does not need the TID field in the request, we
    //      use it to transport the identifier of the specific hardware
    //      prefetcher.
    //      This way we share the same SID for all HW prefetchers. Using
    //      different SIDs means that we need different ports to the cache and
    //      we actually want to reduce those.
    always_comb
    begin : resp_demux
        for (int unsigned i = 0; i < NUM_HW_PREFETCH; i++) begin
            hwpf_stride_rsp_valid_o[i] = hpdcache_rsp_valid_i &&
                                         (i == hpdcache_uint32'(hpdcache_rsp_i.tid));
            hwpf_stride_rsp_o[i] = hpdcache_rsp_i;
        end
    end
    //  }}}
endmodule
