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
 *  Creation Date : September, 2024
 *  Description   : Data Resizer
 *  History       :
m*/
module hpdcache_data_resize
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
    output rdata_t rdata_o,
    output logic   rlast_o
);
//  }}}

//  Upsizer
//  {{{
if (WR_WIDTH < RD_WIDTH) begin : gen_upsize
    hpdcache_data_upsize #(
        .WR_WIDTH       (WR_WIDTH),
        .RD_WIDTH       (RD_WIDTH),
        .DEPTH          (DEPTH)
    ) upsizer_i(
        .clk_i,
        .rst_ni,

        .w_i,
        .wlast_i,
        .wok_o,
        .wdata_i,

        .r_i,
        .rok_o,
        .rdata_o
    );

    assign rlast_o = 1'b1;
end
//  }}}
//  Downsizer
//  {{{
else if (WR_WIDTH > RD_WIDTH) begin : gen_downsize
    hpdcache_data_downsize #(
        .WR_WIDTH       (WR_WIDTH),
        .RD_WIDTH       (RD_WIDTH),
        .DEPTH          (DEPTH)
    ) downsize_i(
        .clk_i,
        .rst_ni,

        .w_i,
        .wok_o,
        .wdata_i,

        .r_i,
        .rok_o,
        .rdata_o,
        .rlast_o
    );
end
//  }}}
//  FIFO
//  {{{
else begin : gen_noresize
    hpdcache_fifo_reg #(
        .FIFO_DEPTH     (DEPTH),
        .FEEDTHROUGH    (1'b0),
        .fifo_data_t    (wdata_t)
    ) fifo_i(
        .clk_i,
        .rst_ni,

        .w_i,
        .wok_o,
        .wdata_i,

        .r_i,
        .rok_o,
        .rdata_o
    );

    assign rlast_o = 1'b1;
end
//  }}}

endmodule
//  }}}
