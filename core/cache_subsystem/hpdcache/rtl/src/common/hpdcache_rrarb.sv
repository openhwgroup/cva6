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
/**
 *  Author(s)     : Cesar Fuguet
 *  Creation Date : April, 2021
 *  Description   : Round-Robin Arbiter
 *                  Based on design from
 *                  http://www.rtlery.com/articles/how-design-round-robin-arbiter
 *  History       :
 */
module hpdcache_rrarb
    //  Parameters
    //  {{{
#(
    //    Number of requesters
    parameter int unsigned N = 0
)
    //  }}}
    //  Ports
    //  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic [N-1:0]          req_i,
    output logic [N-1:0]          gnt_o,
    input  logic                  ready_i
);
    //  }}}

    //  Declaration of internal wires and registers
    //  {{{
    logic [N-1:0]       gnt_q, gnt;
    logic [N-1:0]       nxt;
    logic               wait_q;
    logic [N-1:0]       mask, gnt_msk, gnt_nomsk;
    logic               pending;
    genvar              gen_i;
    //  }}}

    //  Elaboration-time assertions
    //  {{{
`ifndef HPDCACHE_ASSERT_OFF
    initial
    begin : initial_assertions
        n_assertion : assert (N > 0) else $fatal("N must be greater than 0");
    end
`endif
    //  }}}

    //  Compute the thermometer mask vector
    //  {{{
    generate
        if (N > 1) begin : gen_nxt_gt_1
            assign nxt = {gnt_q[N-2:0], gnt_q[N-1]};
        end else begin : gen_nxt_1
            assign nxt = gnt_q[0];
        end

        for (gen_i = 0; gen_i < int'(N); gen_i++) begin : gen_mask
            assign mask[gen_i] = |nxt[gen_i:0];
        end
    endgenerate
    //  }}}

    //  Compute the grant vector
    //  {{{
    hpdcache_prio_1hot_encoder #(.N(N)) prio_msk_i   (.val_i(req_i & mask), .val_o(gnt_msk));
    hpdcache_prio_1hot_encoder #(.N(N)) prio_nomsk_i (.val_i(req_i)       , .val_o(gnt_nomsk));
    assign gnt = |gnt_msk ? gnt_msk : gnt_nomsk;
    //  }}}

    //  Compute the output grant vector
    //  {{{
    assign gnt_o = wait_q ? gnt_q : gnt;
    //  }}}

    //  Setting of internal state
    //  {{{
    assign pending = |req_i;

    always_ff @(posedge clk_i or negedge rst_ni)
    begin
        if (!rst_ni) begin
            wait_q <= 1'b0;
            gnt_q  <= {1'b1, {N-1{1'b0}}};
        end else begin
            wait_q <= ~ready_i & (wait_q | pending);
            if (!wait_q && pending) begin
                gnt_q <= gnt;
            end
        end
    end
    //  }}}

    //  Assertions
    //  {{{
`ifndef HPDCACHE_ASSERT_OFF
    gnt_at_most_one_requester: assert property (@(posedge clk_i) disable iff (!rst_ni)
            $onehot0(gnt)) else $error("arbiter: granting more than one requester");
    gnt_q_exactly_one_requester: assert property (@(posedge clk_i) disable iff (!rst_ni)
            $onehot(gnt_q)) else $error("arbiter: grant state is not one-hot");
`endif
    //  }}}

endmodule
