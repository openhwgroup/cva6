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
 *  Creation Date : November 22, 2022
 *  Description   : Refill data upsize
 *  History       :
 */
module hpdcache_data_upsize
//  {{{
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter int WR_WIDTH = 0,
    parameter int RD_WIDTH = 0,
    parameter int DEPTH    = 0,

    localparam type wdata_t = logic [WR_WIDTH-1:0],
    localparam type rdata_t = logic [RD_WIDTH-1:0]
)
//  }}}
//  Ports
//  {{{
(
    input  logic   clk_i,
    input  logic   rst_ni,

    input  logic   w_i,
    output logic   wok_o,
    input  wdata_t wdata_i,
    input  logic   wlast_i,

    input  logic   r_i,
    output logic   rok_o,
    output rdata_t rdata_o
);
//  }}}
//  Architecture
//  {{{
    //  Local definitions
    //  {{{
    localparam int WR_WORDS = RD_WIDTH/WR_WIDTH;
    localparam int PTR_WIDTH = $clog2(DEPTH);
    localparam int WORDCNT_WIDTH = $clog2(WR_WORDS);
    typedef logic [PTR_WIDTH-1:0]  bufptr_t;
    typedef logic [WORDCNT_WIDTH-1:0]  wordptr_t;
    typedef logic [PTR_WIDTH:0]  occupancy_t;
    //  }}}

    //  Internal registers and signals
    //  {{{
    wdata_t [DEPTH-1:0][WR_WORDS-1:0] buf_q;
    bufptr_t  wrptr_q, wrptr_d;
    bufptr_t  rdptr_q, rdptr_d;
    occupancy_t  used_q, used_d;
    wordptr_t [DEPTH-1:0]  words_q, words_d;
    logic  full, empty;
    logic  shift;
    //  }}}

    //  Control-Path
    //  {{{
    assign full = (hpdcache_uint'(used_q) == DEPTH),
           empty = (used_q == 0),
           wok_o = ~full,
           rok_o = ~empty;

    always_comb
    begin : ctrl_comb
        automatic logic used_inc, used_dec;
        automatic logic words_inc, words_reset;

        wrptr_d = wrptr_q;
        rdptr_d = rdptr_q;
        words_d = words_q;
        used_dec = 1'b0;
        used_inc = 1'b0;
        words_reset = 1'b0;
        words_inc = 1'b0;
        shift = 1'b0;

        if (w_i && wok_o) begin
            shift = 1'b1;
            words_inc = (hpdcache_uint'(words_q[wrptr_q]) < (WR_WORDS-1));
            if (hpdcache_uint'(words_q[wrptr_q]) == (WR_WORDS-1) || wlast_i) begin
                used_inc = 1'b1;
                if (hpdcache_uint'(wrptr_q) == (DEPTH-1)) begin
                    wrptr_d = 0;
                end else begin
                    wrptr_d = wrptr_q + 1;
                end
            end
        end

        if (r_i && rok_o) begin
            used_dec = 1'b1;
            words_reset = 1'b1;
            if (hpdcache_uint'(rdptr_q) == (DEPTH-1)) begin
                rdptr_d = 0;
            end else begin
                rdptr_d = rdptr_q + 1;
            end
        end

        case ({used_inc, used_dec})
            2'b10  : used_d = used_q + 1;
            2'b01  : used_d = used_q - 1;
            default: used_d = used_q;
        endcase

        if (words_inc)   words_d[wrptr_q] = words_q[wrptr_q] + 1;
        if (words_reset) words_d[rdptr_q] = 0;
    end


    always_ff @(posedge clk_i or negedge rst_ni)
    begin : ctrl_ff
        if (!rst_ni) begin
            rdptr_q <= 0;
            wrptr_q <= 0;
            used_q <= 0;
            words_q <= '0;
        end else begin
            rdptr_q <= rdptr_d;
            wrptr_q <= wrptr_d;
            used_q <= used_d;
            words_q <= words_d;
        end
    end
    //  }}}

    //  Data-Path
    //  {{{
    always_ff @(posedge clk_i or negedge rst_ni)
    begin : buf_ff
        if (!rst_ni) begin
            buf_q <= '0;
        end else begin
            if (shift) begin
                buf_q[wrptr_q][words_q[wrptr_q]] <= wdata_i;
            end
        end
    end

    assign rdata_o = buf_q[rdptr_q];
    //  }}}

    //  Assertions
    //  {{{
`ifndef HPDCACHE_ASSERT_OFF
    initial
    begin : initial_assertions
        assert  (DEPTH     >        0)       else $error("DEPTH must be greater than 0");
        assert  (WR_WIDTH  >        0)       else $error("WR_WIDTH must be greater than 0");
        assert  (RD_WIDTH  >        0)       else $error("RD_WIDTH must be greater than 0");
        assert  (WR_WIDTH  < RD_WIDTH)       else $error("WR_WIDTH must be less to RD_WIDTH");
        assert ((RD_WIDTH  % WR_WIDTH) == 0) else $error("RD_WIDTH must be a multiple WR_WIDTH");
    end
`endif
    //  }}}
//  }}}
endmodule
//  }}}
