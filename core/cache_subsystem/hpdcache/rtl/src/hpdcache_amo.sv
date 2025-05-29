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
 *  Creation Date : May, 2021
 *  Description   : HPDcache AMO computing unit
 *  History       :
 */
module hpdcache_amo
import hpdcache_pkg::*;
//  Ports
//  {{{
(
    input  logic [63:0]           ld_data_i,
    input  logic [63:0]           st_data_i,
    input  hpdcache_uc_op_t       op_i,
    output logic [63:0]           result_o
);
//  }}}

    logic signed [63:0] ld_data;
    logic signed [63:0] st_data;
    logic signed [63:0] sum;
    logic               ugt, sgt;

    assign ld_data = ld_data_i,
           st_data = st_data_i;

    assign ugt = (ld_data_i > st_data_i),
           sgt = (ld_data   > st_data),
           sum =  ld_data   + st_data;

    always_comb
    begin : amo_compute_comb
        unique case (1'b1)
            op_i.is_amo_lr   : result_o = ld_data_i;
            op_i.is_amo_sc   : result_o = st_data_i;
            op_i.is_amo_swap : result_o = st_data_i;
            op_i.is_amo_add  : result_o = sum;
            op_i.is_amo_and  : result_o = ld_data_i & st_data_i;
            op_i.is_amo_or   : result_o = ld_data_i | st_data_i;
            op_i.is_amo_xor  : result_o = ld_data_i ^ st_data_i;
            op_i.is_amo_max  : result_o = sgt ? ld_data_i : st_data_i;
            op_i.is_amo_maxu : result_o = ugt ? ld_data_i : st_data_i;
            op_i.is_amo_min  : result_o = sgt ? st_data_i : ld_data_i;
            op_i.is_amo_minu : result_o = ugt ? st_data_i : ld_data_i;
            default          : result_o = '0;
        endcase
    end
endmodule
