// 
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVMT_OBI_ST_DUT_WRAP_SV__
`define __UVMT_OBI_ST_DUT_WRAP_SV__


/**
 * Module wrapper for Open Bus Interface RTL DUT. All ports are SV interfaces.
 */
module uvmt_obi_st_dut_wrap(
   uvma_obi_if  mstr_if,
   uvma_obi_if  slv_if
);
   assign slv_if.req    = mstr_if.req   ;
   assign slv_if.addr   = mstr_if.addr  ;
   assign slv_if.we     = mstr_if.we    ;
   assign slv_if.be     = mstr_if.be    ;
   assign slv_if.wdata  = mstr_if.wdata ;
   assign slv_if.auser  = mstr_if.auser ;
   assign slv_if.wuser  = mstr_if.wuser ;
   assign slv_if.aid    = mstr_if.aid   ;
   assign slv_if.rready = mstr_if.rready;
   
   assign mstr_if.gnt    = slv_if.gnt   ;
   assign mstr_if.rvalid = slv_if.rvalid;
   assign mstr_if.rdata  = slv_if.rdata ;
   assign mstr_if.err    = slv_if.err   ;
   assign mstr_if.ruser  = slv_if.ruser ;
   assign mstr_if.rid    = slv_if.rid   ;
   
endmodule : uvmt_obi_st_dut_wrap


`endif // __UVMT_OBI_ST_DUT_WRAP_SV__
