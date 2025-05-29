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
 *  Description   : Dcache Memory Write Channels Arbiter
 *  History       :
 */
module hpdcache_mem_req_write_arbiter
//  Parameters
//  {{{
#(
    parameter int unsigned N = 0,
    parameter type hpdcache_mem_req_t = logic,
    parameter type hpdcache_mem_req_w_t = logic
)
//  }}}
//  Ports
//  {{{
(
    input  logic                        clk_i,
    input  logic                        rst_ni,

    output logic                [N-1:0] mem_req_write_ready_o,
    input  logic                [N-1:0] mem_req_write_valid_i,
    input  hpdcache_mem_req_t   [N-1:0] mem_req_write_i,

    output logic                [N-1:0] mem_req_write_data_ready_o,
    input  logic                [N-1:0] mem_req_write_data_valid_i,
    input  hpdcache_mem_req_w_t [N-1:0] mem_req_write_data_i,

    input  logic                        mem_req_write_ready_i,
    output logic                        mem_req_write_valid_o,
    output hpdcache_mem_req_t           mem_req_write_o,

    input  logic                        mem_req_write_data_ready_i,
    output logic                        mem_req_write_data_valid_o,
    output hpdcache_mem_req_w_t         mem_req_write_data_o
);
//  }}}

    //  Types and wires
    //  {{{
    typedef logic [N-1:0] arb_gnt_t;

    logic                        req_valid, req_data_valid, req_data_last;

    arb_gnt_t                    mem_write_arb_req_data_last;
    arb_gnt_t                    mem_write_arb_req_gnt, mem_write_arb_req_gnt_q;

    logic                        mem_write_arb_req_r, mem_write_arb_req_w;
    logic                        mem_write_arb_req_rok, mem_write_arb_req_wok;
    logic                        mem_write_arb_req_ready;

    logic                        mem_req_write_w;
    logic                        mem_req_write_wok;
    hpdcache_mem_req_t           mem_req_write;

    genvar                       gen_i;
    //  }}}

    //  Combinational logic
    //  {{{
    for (gen_i = 0; gen_i < int'(N); gen_i++) begin : gen_bitvectors
        assign mem_write_arb_req_data_last[gen_i] = mem_req_write_data_i[gen_i].mem_req_w_last;

        assign mem_req_write_ready_o[gen_i] = mem_write_arb_req_gnt[gen_i] &
                                              mem_write_arb_req_ready;

        assign mem_req_write_data_ready_o[gen_i] = mem_write_arb_req_gnt_q[gen_i] &
                                                   mem_write_arb_req_rok &
                                                   mem_req_write_data_ready_i;
    end

    assign req_valid      = |(mem_write_arb_req_gnt   & mem_req_write_valid_i);
    assign req_data_valid = |(mem_write_arb_req_gnt_q & mem_req_write_data_valid_i);
    assign req_data_last  = |(mem_write_arb_req_gnt_q & mem_write_arb_req_data_last);

    //  Accept a new request when the grant FIFO is not full and the NoC can accept the request
    assign mem_write_arb_req_ready = mem_write_arb_req_wok & mem_req_write_wok;

    //  Write a grant decision into the FIFO
    assign mem_write_arb_req_w = req_valid & mem_req_write_wok;

    //  Read grant FIFO when the NoC is able to receive the data and it is the last flit of data
    assign mem_write_arb_req_r = mem_req_write_data_ready_i &
                                 mem_write_arb_req_rok &
                                 req_data_valid &
                                 req_data_last;

    //  Accept a new request when the grant FIFO is not full and the NoC can accept the request
    assign mem_req_write_w = req_valid & mem_write_arb_req_wok;

    //  Forward the data to the NoC if there is any and there is a grant decision in the FIFO
    assign mem_req_write_data_valid_o = req_data_valid & mem_write_arb_req_rok;
    //  }}}

    //  Fixed-priority arbiter
    //  {{{
    hpdcache_fxarb #(
        .N             (N)
    ) hpdcache_fxarb_mem_req_write_i(
        .clk_i,
        .rst_ni,
        .req_i         (mem_req_write_valid_i),
        .gnt_o         (mem_write_arb_req_gnt),
        .ready_i       (mem_write_arb_req_ready)
    );
    //  }}}

    //  Request FIFO
    //  {{{
    hpdcache_fifo_reg #(
        .FIFO_DEPTH    (1),
        .FEEDTHROUGH   (1'b1),
        .fifo_data_t   (hpdcache_mem_req_t)
    ) req_fifo_i(
        .clk_i,
        .rst_ni,
        .w_i           (mem_req_write_w),
        .wok_o         (mem_req_write_wok),
        .wdata_i       (mem_req_write),
        .r_i           (mem_req_write_ready_i),
        .rok_o         (mem_req_write_valid_o),
        .rdata_o       (mem_req_write_o)
    );
    //  }}}

    //  Grant signal FIFO
    //  {{{
    hpdcache_fifo_reg #(
        .FIFO_DEPTH    (2),
        .FEEDTHROUGH   (1'b1),
        .fifo_data_t   (arb_gnt_t)
    ) req_gnt_fifo_i(
        .clk_i,
        .rst_ni,
        .w_i           (mem_write_arb_req_w),
        .wok_o         (mem_write_arb_req_wok),
        .wdata_i       (mem_write_arb_req_gnt),
        .r_i           (mem_write_arb_req_r),
        .rok_o         (mem_write_arb_req_rok),
        .rdata_o       (mem_write_arb_req_gnt_q)
    );
    //  }}}

    //  Mux requests
    //  {{{
    hpdcache_mux #(
        .NINPUT        (N),
        .DATA_WIDTH    ($bits(hpdcache_mem_req_t)),
        .ONE_HOT_SEL   (1'b1)
    ) req_mux_i(
        .data_i        (mem_req_write_i),
        .sel_i         (mem_write_arb_req_gnt),
        .data_o        (mem_req_write)
    );
    //  }}}

    //  Mux data
    //  {{{
    hpdcache_mux #(
        .NINPUT        (N),
        .DATA_WIDTH    ($bits(hpdcache_mem_req_w_t)),
        .ONE_HOT_SEL   (1'b1)
    ) data_mux_i(
        .data_i        (mem_req_write_data_i),
        .sel_i         (mem_write_arb_req_gnt_q),
        .data_o        (mem_req_write_data_o)
    );
    //  }}}

endmodule
