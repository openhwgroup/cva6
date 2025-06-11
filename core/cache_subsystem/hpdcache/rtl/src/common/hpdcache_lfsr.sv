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
 *  Author(s)     : Cesar Fuguet
 *  Creation Date : Mars, 2024
 *  Description   : Galois Linear Feedback Shift Register
 *  History       :
 */
module hpdcache_lfsr
//  Parameters
//  {{{
#(
    parameter int WIDTH = 8,

    localparam type data_t = logic [WIDTH-1:0]
)
//  }}}

//  Ports
//  {{{
(
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        shift_i,
    output data_t       val_o
);
//  }}}

//  Feedback Polynomial
//  {{{
logic [15:0] polynomial;

assign polynomial = (WIDTH ==  8) ? 16'h00E1 :
                    (WIDTH ==  9) ? 16'h01EA :
                    (WIDTH == 10) ? 16'h02E3 :
                    (WIDTH == 11) ? 16'h04E3 :
                    (WIDTH == 12) ? 16'h0AE2 :
                    (WIDTH == 13) ? 16'h10E3 :
                    (WIDTH == 14) ? 16'h20EA :
                    (WIDTH == 15) ? 16'h41E2 :
                    (WIDTH == 16) ? 16'h81EE : 16'h0BAD;
//  }}}

//  Linear Feedback Shift Register
//  {{{
data_t lfsr_q, lfsr_d;
data_t lfsr_shifted;

assign lfsr_shifted = {1'b0, lfsr_q[WIDTH-1:1]};

always_comb
begin : lfsr_comb
    if (lfsr_q[0]) lfsr_d = lfsr_shifted ^ polynomial[WIDTH-1:0];
    else           lfsr_d = lfsr_shifted;
end

assign val_o = lfsr_q;

always_ff @(posedge clk_i or negedge rst_ni)
begin : lfsr_ff
    if (!rst_ni) begin
        lfsr_q <= '1;
    end else begin
        if (shift_i) lfsr_q <= lfsr_d;
    end
end
//  }}}

//  Assertions
//  {{{
`ifndef HPDCACHE_ASSERT_OFF
initial begin : assertions_initials
    assert ((WIDTH >= 8) && (WIDTH <= 16)) else $fatal("illegal width");
end
`endif
//  }}}

endmodule
