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
 *  Description   : Dcache Memory Read Request Channel Arbiter
 *  History       :
 */
module hpdcache_mem_req_read_arbiter
//  Parameters
//  {{{
#(
    parameter int unsigned N = 0,
    parameter type hpdcache_mem_req_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input  logic                      clk_i,
    input  logic                      rst_ni,

    output logic              [N-1:0] mem_req_read_ready_o,
    input  logic              [N-1:0] mem_req_read_valid_i,
    input  hpdcache_mem_req_t [N-1:0] mem_req_read_i,

    input  logic                      mem_req_read_ready_i,
    output logic                      mem_req_read_valid_o,
    output hpdcache_mem_req_t         mem_req_read_o
);
//  }}}

    logic              [N-1:0] mem_read_arb_req_gnt;

    logic                      req_valid;

    genvar                     gen_i;

    assign req_valid = |(mem_read_arb_req_gnt & mem_req_read_valid_i);

    //  Fixed-priority arbiter
    hpdcache_fxarb #(
        .N                   (N)
    ) hpdcache_fxarb_mem_req_write_i (
        .clk_i,
        .rst_ni,
        .req_i               (mem_req_read_valid_i),
        .gnt_o               (mem_read_arb_req_gnt),
        .ready_i             (mem_req_read_ready_i)
    );

    //  Demultiplexor for the ready signal
    for (gen_i = 0; gen_i < int'(N); gen_i++) begin : gen_req_ready
        assign mem_req_read_ready_o[gen_i] = mem_req_read_ready_i & mem_read_arb_req_gnt[gen_i] &
                                             mem_req_read_valid_i[gen_i];
    end

    assign mem_req_read_valid_o = req_valid;

    //  Multiplexor for requests
    hpdcache_mux #(
        .NINPUT              (N),
        .DATA_WIDTH          ($bits(hpdcache_mem_req_t)),
        .ONE_HOT_SEL         (1'b1)
    ) mem_read_req_mux_i (
        .data_i              (mem_req_read_i),
        .sel_i               (mem_read_arb_req_gnt),
        .data_o              (mem_req_read_o)
    );

endmodule
