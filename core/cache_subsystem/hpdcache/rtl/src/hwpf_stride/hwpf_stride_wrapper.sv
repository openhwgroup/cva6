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
 *  Authors       : Riccardo Alidori, Cesar Fuguet
 *  Creation Date : June, 2021
 *  Description   : Linear Hardware Memory Prefetcher wrapper.
 *  History       :
 */
`include "hpdcache_typedef.svh"

module hwpf_stride_wrapper
import hwpf_stride_pkg::*;
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,
    parameter int unsigned NUM_HW_PREFETCH = 4,
    parameter int unsigned NUM_SNOOP_PORTS = 1,

    //  Request Interface Definitions
    //  {{{
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_req_offset_t = logic,
    parameter type hpdcache_req_data_t = logic,
    parameter type hpdcache_req_be_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_tid_t = logic,
    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic
    //  }}}
)
//  }}}

//  Ports
//  {{{
(
    input  logic                                        clk_i,
    input  logic                                        rst_ni,

    //  CSR
    //  {{{
    input  logic                  [NUM_HW_PREFETCH-1:0] hwpf_stride_base_set_i,
    input  hwpf_stride_base_t     [NUM_HW_PREFETCH-1:0] hwpf_stride_base_i,
    output hwpf_stride_base_t     [NUM_HW_PREFETCH-1:0] hwpf_stride_base_o,

    input  logic                  [NUM_HW_PREFETCH-1:0] hwpf_stride_param_set_i,
    input  hwpf_stride_param_t    [NUM_HW_PREFETCH-1:0] hwpf_stride_param_i,
    output hwpf_stride_param_t    [NUM_HW_PREFETCH-1:0] hwpf_stride_param_o,

    input  logic                  [NUM_HW_PREFETCH-1:0] hwpf_stride_throttle_set_i,
    input  hwpf_stride_throttle_t [NUM_HW_PREFETCH-1:0] hwpf_stride_throttle_i,
    output hwpf_stride_throttle_t [NUM_HW_PREFETCH-1:0] hwpf_stride_throttle_o,

    output hwpf_stride_status_t                         hwpf_stride_status_o,
    //  }}}

    // Snooping
    //  {{{
    input  logic                 [NUM_SNOOP_PORTS-1:0]  snoop_valid_i,
    input  logic                 [NUM_SNOOP_PORTS-1:0]  snoop_abort_i,
    input  hpdcache_req_offset_t [NUM_SNOOP_PORTS-1:0]  snoop_addr_offset_i,
    input  hpdcache_tag_t        [NUM_SNOOP_PORTS-1:0]  snoop_addr_tag_i,
    input  logic                 [NUM_SNOOP_PORTS-1:0]  snoop_phys_indexed_i,
    //  }}}

    //  Dcache interface
    //  {{{
    input  hpdcache_req_sid_t                           hpdcache_req_sid_i,
    output logic                                        hpdcache_req_valid_o,
    input  logic                                        hpdcache_req_ready_i,
    output hpdcache_req_t                               hpdcache_req_o,
    output logic                                        hpdcache_req_abort_o,
    output hpdcache_tag_t                               hpdcache_req_tag_o,
    output hpdcache_pma_t                               hpdcache_req_pma_o,
    input  logic                                        hpdcache_rsp_valid_i,
    input  hpdcache_rsp_t                               hpdcache_rsp_i
    //  }}}
);
//  }}}

    //  Internal registers
    //  {{{
    typedef logic [HPDcacheCfg.nlineWidth-1:0] hpdcache_nline_t;
    typedef logic [HPDcacheCfg.setWidth-1:0] hpdcache_set_t;
    //  }}}

    //  Internal registers
    //  {{{
    logic                 [NUM_SNOOP_PORTS-1:0] snoop_valid_q;
    hpdcache_req_offset_t [NUM_SNOOP_PORTS-1:0] snoop_addr_offset_q;
    //  }}}

    //  Internal signals
    //  {{{
    logic            [NUM_HW_PREFETCH-1:0] hwpf_stride_enable;
    logic            [NUM_HW_PREFETCH-1:0] hwpf_stride_free;
    logic            [NUM_HW_PREFETCH-1:0] hwpf_stride_status_busy;
    logic            [3:0]                 hwpf_stride_status_free_idx;

    hpdcache_nline_t [NUM_HW_PREFETCH-1:0] hwpf_snoop_nline;
    logic            [NUM_HW_PREFETCH-1:0] hwpf_snoop_match;

    logic            [NUM_HW_PREFETCH-1:0] hwpf_stride_req_valid;
    logic            [NUM_HW_PREFETCH-1:0] hwpf_stride_req_ready;
    hpdcache_req_t   [NUM_HW_PREFETCH-1:0] hwpf_stride_req;

    logic            [NUM_HW_PREFETCH-1:0] hwpf_stride_arb_in_req_valid;
    logic            [NUM_HW_PREFETCH-1:0] hwpf_stride_arb_in_req_ready;
    hpdcache_req_t   [NUM_HW_PREFETCH-1:0] hwpf_stride_arb_in_req;
    logic            [NUM_HW_PREFETCH-1:0] hwpf_stride_arb_in_rsp_valid;
    hpdcache_rsp_t   [NUM_HW_PREFETCH-1:0] hwpf_stride_arb_in_rsp;
    //  }}}

    //  Assertions
    //  {{{
    //  pragma translate_off
    initial
    begin : initial_assertions
        max_hwpf_stride_assert: assert (NUM_HW_PREFETCH <= 16) else
                $error("hwpf_stride: maximum number of HW prefetchers is 16");
    end
    //  pragma translate_on
    //  }}}

    //  Compute the status information
    //  {{{
    always_comb begin: hwpf_stride_priority_encoder
        hwpf_stride_status_free_idx = '0;
        for (int unsigned i = 0; i < NUM_HW_PREFETCH; i++) begin
            if (hwpf_stride_free[i]) begin
                hwpf_stride_status_free_idx = i;
                break;
            end
        end
    end

    //     Free flag of engines
    assign hwpf_stride_free            = ~(hwpf_stride_enable | hwpf_stride_status_busy);
    //     Busy flags
    assign hwpf_stride_status_o[63:32] = {{32-NUM_HW_PREFETCH{1'b0}}, hwpf_stride_status_busy};
    //     Global free flag
    assign hwpf_stride_status_o[31]    = |hwpf_stride_free;
    //     Free Index
    assign hwpf_stride_status_o[30:16] = {11'b0, hwpf_stride_status_free_idx};
    //     Enable flags
    assign hwpf_stride_status_o[15:0]  = {{16-NUM_HW_PREFETCH{1'b0}}, hwpf_stride_enable};
    //  }}}

    //  Hardware prefetcher engines
    //  {{{
    for (genvar j = 0; j < NUM_SNOOP_PORTS; j++) begin : gen_hwpf_snoop
        always_ff @(posedge clk_i or negedge rst_ni)
        begin : snoop_ff
            if (!rst_ni) begin
                snoop_valid_q[j]       <= 1'b0;
                snoop_addr_offset_q[j] <= '0;
            end else begin
                if (snoop_phys_indexed_i[j]) begin
                    snoop_valid_q[j]       <= snoop_valid_i[j];
                    snoop_addr_offset_q[j] <= snoop_addr_offset_i[j];
                end
            end
        end
    end

    for (genvar i = 0; i < NUM_HW_PREFETCH; i++) begin : gen_hwpf_stride
        assign hwpf_stride_enable[i] = hwpf_stride_base_o[i].enable;

        //  Compute snoop match signals
        //  {{{
        always_comb
        begin : snoop_comb
            hwpf_snoop_match[i] = 1'b0;
            for (int j = 0; j < NUM_SNOOP_PORTS; j++) begin
                automatic logic                 snoop_valid;
                automatic hpdcache_req_offset_t snoop_offset;
                automatic hpdcache_nline_t      snoop_nline;

                if (snoop_phys_indexed_i[j]) begin
                    snoop_valid  = snoop_valid_i[j];
                    snoop_offset = snoop_addr_offset_i[j];
                end else begin
                    snoop_valid  = snoop_valid_q[j];
                    snoop_offset = snoop_addr_offset_q[j];
                end
                snoop_nline = {snoop_addr_tag_i[j], snoop_offset};
                hwpf_snoop_match[i] |= (snoop_valid         && !snoop_abort_i[j] &&
                                       (hwpf_snoop_nline[i] ==  snoop_nline));
            end
        end
        //  }}}

        hwpf_stride #(
            .HPDcacheCfg          (HPDcacheCfg),
            .hpdcache_nline_t     (hpdcache_nline_t),
            .hpdcache_tag_t       (hpdcache_tag_t),
            .hpdcache_set_t       (hpdcache_set_t),
            .hpdcache_req_t       (hpdcache_req_t),
            .hpdcache_rsp_t       (hpdcache_rsp_t)
        ) hwpf_stride_i(
            .clk_i,
            .rst_ni,

            .csr_base_set_i       (hwpf_stride_base_set_i[i]),
            .csr_base_i           (hwpf_stride_base_i[i]),
            .csr_param_set_i      (hwpf_stride_param_set_i[i]),
            .csr_param_i          (hwpf_stride_param_i[i]),
            .csr_throttle_set_i   (hwpf_stride_throttle_set_i[i]),
            .csr_throttle_i       (hwpf_stride_throttle_i[i]),

            .csr_base_o           (hwpf_stride_base_o[i]),
            .csr_param_o          (hwpf_stride_param_o[i]),
            .csr_throttle_o       (hwpf_stride_throttle_o[i]),

            .busy_o               (hwpf_stride_status_busy[i]),

            .snoop_nline_o        (hwpf_snoop_nline[i]),
            .snoop_match_i        (hwpf_snoop_match[i]),

            .hpdcache_req_valid_o (hwpf_stride_req_valid[i]),
            .hpdcache_req_ready_i (hwpf_stride_req_ready[i]),
            .hpdcache_req_o       (hwpf_stride_req[i]),
            .hpdcache_rsp_valid_i (hwpf_stride_arb_in_rsp_valid[i]),
            .hpdcache_rsp_i       (hwpf_stride_arb_in_rsp[i])
        );

        assign hwpf_stride_req_ready[i]               = hwpf_stride_arb_in_req_ready[i],
               hwpf_stride_arb_in_req_valid[i]        = hwpf_stride_req_valid[i],
               hwpf_stride_arb_in_req[i].addr_offset  = hwpf_stride_req[i].addr_offset,
               hwpf_stride_arb_in_req[i].wdata        = hwpf_stride_req[i].wdata,
               hwpf_stride_arb_in_req[i].op           = hwpf_stride_req[i].op,
               hwpf_stride_arb_in_req[i].be           = hwpf_stride_req[i].be,
               hwpf_stride_arb_in_req[i].size         = hwpf_stride_req[i].size,
               hwpf_stride_arb_in_req[i].sid          = hpdcache_req_sid_i,
               hwpf_stride_arb_in_req[i].tid          = hpdcache_req_tid_t'(i),
               hwpf_stride_arb_in_req[i].need_rsp     = hwpf_stride_req[i].need_rsp,
               hwpf_stride_arb_in_req[i].phys_indexed = hwpf_stride_req[i].phys_indexed,
               hwpf_stride_arb_in_req[i].addr_tag     = '0,
               hwpf_stride_arb_in_req[i].pma          = '0;
    end
    //  }}}

    //  Hardware prefetcher arbiter betweem engines
    //  {{{
    hwpf_stride_arb #(
        .NUM_HW_PREFETCH          (NUM_HW_PREFETCH),
        .hpdcache_req_t           (hpdcache_req_t),
        .hpdcache_rsp_t           (hpdcache_rsp_t)
    ) hwpf_stride_arb_i (
        .clk_i,
        .rst_ni,

        // DCache input interface
        .hwpf_stride_req_valid_i  (hwpf_stride_arb_in_req_valid),
        .hwpf_stride_req_ready_o  (hwpf_stride_arb_in_req_ready),
        .hwpf_stride_req_i        (hwpf_stride_arb_in_req),
        .hwpf_stride_rsp_valid_o  (hwpf_stride_arb_in_rsp_valid),
        .hwpf_stride_rsp_o        (hwpf_stride_arb_in_rsp),

        // DCache output interface
        .hpdcache_req_valid_o,
        .hpdcache_req_ready_i,
        .hpdcache_req_o,
        .hpdcache_rsp_valid_i,
        .hpdcache_rsp_i
    );

    assign hpdcache_req_abort_o = 1'b0,  // unused on physically indexed requests
           hpdcache_req_tag_o   = '0,    // unused on physically indexed requests
           hpdcache_req_pma_o   = '0;    // unused on physically indexed requests
    //  }}}

endmodule
