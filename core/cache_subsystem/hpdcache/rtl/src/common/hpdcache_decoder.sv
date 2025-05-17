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
 *  Description   : Decoder
 *  History       :
 */
module hpdcache_decoder
    //  Parameters
    //  {{{
#(
    parameter  int unsigned N     = 0,
    localparam int unsigned Pow2N = 2**N,
    localparam type in_t  = logic unsigned [N-1:0],
    localparam type out_t = logic unsigned [Pow2N-1:0]
)
    //  }}}

    //  Ports
    //  {{{
(
    input  logic   en_i,
    input  in_t    val_i,
    output out_t   val_o
);
    //  }}}

    always_comb
    begin : decoder_comb
        val_o = 0;
        for (int unsigned i = 0; i < Pow2N; i++) begin
            if (val_i == in_t'(i)) val_o[i] = en_i;
        end
    end
endmodule
