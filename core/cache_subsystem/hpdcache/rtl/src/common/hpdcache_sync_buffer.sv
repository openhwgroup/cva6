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
 *  Creation Date : October, 2023
 *  Description   : Synchronization buffer
 *  History       :
 */
module hpdcache_sync_buffer
    //  Parameters
    //  {{{
#(
    parameter bit FEEDTHROUGH = 1'b0,
    parameter type data_t = logic
)
    //  }}}
    //  Ports
    //  {{{
(
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        w_i,
    output logic        wok_o,
    input  data_t       wdata_i,
    input  logic        r_i,
    output logic        rok_o,
    output data_t       rdata_o
);
    //  }}}

    //  Declaration of internal wires and registers
    //  {{{
    data_t      buf_q;
    logic       buf_we;
    logic       valid_q, valid_d;
    //  }}}

    //  Global control signals
    //  {{{
    assign rok_o  =  valid_q | (FEEDTHROUGH & w_i),
           wok_o  = ~valid_q | (FEEDTHROUGH & r_i);

    assign buf_we = w_i & ((FEEDTHROUGH & ~(valid_q ^ r_i)) | (~FEEDTHROUGH & ~valid_q));
    //  }}}

    //  Control of buffer
    //  {{{
    assign valid_d = buf_we | (valid_q & ~r_i);
    //  }}}

    //  FIFO buffer memory management
    //  {{{
    always_ff @(posedge clk_i)
    begin
        if (buf_we) buf_q <= wdata_i;
    end

    assign rdata_o = FEEDTHROUGH && !valid_q ? wdata_i : buf_q;
    //  }}}

    //  Setting of internal state
    //  {{{
    always_ff @(posedge clk_i or negedge rst_ni)
    begin
        if (!rst_ni) begin
            valid_q <= 1'b0;
        end else begin
            valid_q <= valid_d;
        end
    end
    //  }}}
endmodule
