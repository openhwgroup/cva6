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
 *  Creation Date : April, 2021
 *  Description   : Simple multiplexor
 *  History       :
 */
module hpdcache_mux
    //  Parameters
    //  {{{
#(
    //  Number of inputs
    parameter  int unsigned NINPUT      = 0,

    //  Width in bits of each input
    parameter  int unsigned DATA_WIDTH  = 0,

    //  Selector signal is one-hot encoded
    parameter  bit          ONE_HOT_SEL = 0,

    //  Compute the width of the selection signal
    localparam int unsigned NINPUT_LOG2 = $clog2(NINPUT),
    localparam int unsigned SEL_WIDTH   = ONE_HOT_SEL ? NINPUT : NINPUT_LOG2,

    localparam type data_t = logic [DATA_WIDTH-1:0],
    localparam type sel_t  = logic [SEL_WIDTH-1:0]
)
    //  }}}

    //  Ports
    //  {{{
(
    input  data_t [NINPUT-1:0] data_i,
    input  sel_t               sel_i,
    output data_t              data_o
);
    //  }}}

    typedef int unsigned uint32;

    if (NINPUT == 1) begin : gen_single_input
        assign data_o = data_i[0];

    end else begin : gen_multi_input
        //  Selector is one-hot encoded
        if (ONE_HOT_SEL == 1) begin : gen_onehot_sel
            always_comb
            begin : data_out_mux_comb
                data_o = '0;
                for (int unsigned i = 0; i < NINPUT; i++) begin
                    data_o |= sel_i[i] ? data_i[i] : '0;
                end
            end

        //  Selector is binary encoded
        end else begin : gen_binary_sel
            always_comb
            begin : data_out_mux_comb
                data_o = '0;
                for (int unsigned i = 0; i < NINPUT; i++) begin
                    data_o |= (i == uint32'(sel_i)) ? data_i[i] : '0;
                end
            end
        end
    end
endmodule
