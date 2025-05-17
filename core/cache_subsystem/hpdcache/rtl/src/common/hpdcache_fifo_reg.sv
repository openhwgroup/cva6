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
 *  Description   : FIFO buffer (using registers)
 *  History       :
 */
module hpdcache_fifo_reg
    //  Parameters
    //  {{{
#(
    parameter int unsigned FIFO_DEPTH = 0,
    parameter bit FEEDTHROUGH = 1'b0,
    parameter type fifo_data_t = logic
)
    //  }}}
    //  Ports
    //  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  w_i,
    output logic                  wok_o,
    input  fifo_data_t            wdata_i,
    input  logic                  r_i,
    output logic                  rok_o,
    output fifo_data_t            rdata_o
);
    //  }}}

    //  Declaration of constants, types and functions
    //  {{{
    localparam int __FIFO_DEPTH = FIFO_DEPTH > 1 ? FIFO_DEPTH : 2;
    typedef logic unsigned [$clog2(__FIFO_DEPTH)-1:0] fifo_addr_t;
    //  }}}

    /*
     *  Bypass: no buffering
     */
    if (FIFO_DEPTH == 0) begin : gen_bypass
        assign wok_o   = r_i;
        assign rok_o   = w_i;
        assign rdata_o = wdata_i;

    /*
     *  Single-entry buffer -> synchronization buffer
     */
    end else if (FIFO_DEPTH == 1) begin : gen_buffer
        hpdcache_sync_buffer #(
            .FEEDTHROUGH     (FEEDTHROUGH),
            .data_t          (fifo_data_t)
        ) i_sync_buffer (
            .clk_i,
            .rst_ni,
            .w_i,
            .wok_o,
            .wdata_i,
            .r_i,
            .rok_o,
            .rdata_o
        );

    /*
     *  Multi-entry FIFO buffer
     */
    end else if (FIFO_DEPTH > 1) begin : gen_fifo
        //  Declaration of internal wires and registers
        //  {{{
        fifo_data_t [FIFO_DEPTH-1:0] fifo_mem_q;
        fifo_addr_t rptr_q, rptr_d; // read pointer
        fifo_addr_t wptr_q, wptr_d; // write pointer
        logic       crossover_q, crossover_d; // write pointer has wrap
        logic       rexec, wexec;
        logic       rptr_max, wptr_max;
        logic       match_ptr;
        logic       empty, full;
        //  }}}

        //  Global control signals
        //  {{{
        assign match_ptr = (wptr_q == rptr_q);

        assign empty = match_ptr & ~crossover_q,
               full  = match_ptr &  crossover_q;

        assign rok_o = ~empty | (FEEDTHROUGH & w_i),
               wok_o = ~full  | (FEEDTHROUGH & r_i);

        assign rexec = r_i & ~empty,
               wexec = w_i & (( FEEDTHROUGH & ((empty & ~r_i) | (full & r_i) | (~full & ~empty))) |
                              (~FEEDTHROUGH & ~full));

        //  }}}

        //  Control of read and write pointers
        //  {{{
        assign rptr_max = (rptr_q == fifo_addr_t'(FIFO_DEPTH-1));
        assign wptr_max = (wptr_q == fifo_addr_t'(FIFO_DEPTH-1));

        always_comb
        begin : fifo_ctrl_comb
            rptr_d = rptr_q;
            wptr_d = wptr_q;
            crossover_d = crossover_q;

            if (rexec) begin
                rptr_d = rptr_max ? 0 : rptr_q + 1;
            end

            if (wexec) begin
                wptr_d = wptr_max ? 0 : wptr_q + 1;
            end

            if (wexec && wptr_max) begin
                crossover_d = 1'b1;
            end else if (rexec && rptr_max) begin
                crossover_d = 1'b0;
            end
        end
        //  }}}

        //  FIFO buffer memory management
        //  {{{
        always_ff @(posedge clk_i)
        begin
            if (wexec) fifo_mem_q[wptr_q] <= wdata_i;
        end

        assign rdata_o = FEEDTHROUGH && empty ? wdata_i : fifo_mem_q[rptr_q];
        //  }}}

        //  Setting of internal state
        //  {{{
        always_ff @(posedge clk_i or negedge rst_ni)
        begin
            if (!rst_ni) begin
                rptr_q      <= 0;
                wptr_q      <= 0;
                crossover_q <= 1'b0;
            end else begin
                rptr_q      <= rptr_d;
                wptr_q      <= wptr_d;
                crossover_q <= crossover_d;
            end
        end
        //  }}}

        //  Assertions
        //  {{{
`ifndef HPDCACHE_ASSERT_OFF
        rptr_ahead_wptr_assert: assert property (@(posedge clk_i) disable iff (!rst_ni)
                ((rptr_q <= wptr_q) && !crossover_q) ||
                ((rptr_q >= wptr_q) &&  crossover_q)) else
                $error("fifo: read pointer is ahead of the write pointer");
`endif
        //  }}}
    end
endmodule
