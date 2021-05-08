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


`ifndef __UVMT_OBI_ST_TB_SV__
`define __UVMT_OBI_ST_TB_SV__


/**
 * Module encapsulating the Open Bus Interface VIP Self-Test DUT wrapper,
 * agents and clock generating interfaces. The clock and reset interface only
 * feeds into the Open Bus Interface VIP interfaces.
 */
module uvmt_obi_st_tb;
   
   import uvm_pkg::*;
   import uvmt_obi_st_pkg::*;
   
   // Clocking & Reset
   uvmt_obi_st_clknrst_gen_if  clknrst_gen_if();
   
   // Agent interfaces
   uvma_obi_if  mstr_if(.clk(clknrst_gen_if.clk), .reset_n(clknrst_gen_if.reset_n));
   uvma_obi_if  slv_if (.clk(clknrst_gen_if.clk), .reset_n(clknrst_gen_if.reset_n));
   
   // DUT instance
   uvmt_obi_st_dut_wrap  dut_wrap(.*);
   
   
   /**
    * Test bench entry point.
    */
   initial begin
      // Specify time format for simulation
      $timeformat(
         /*.units_number       (*/   -9/*)*/,
         /*.precision_number   (*/    3/*)*/,
         /*.suffix_string      (*/" ns"/*)*/,
         /*.minimum_field_width(*/   18/*)*/ 
      );
      
      // Add interfaces to uvm_config_db
      uvm_config_db#(virtual uvmt_obi_st_clknrst_gen_if)::set(null, "*"               , "clknrst_gen_vif", clknrst_gen_if);
      uvm_config_db#(virtual uvma_obi_if               )::set(null, "*.env.mstr_agent", "vif"            , mstr_if       );
      uvm_config_db#(virtual uvma_obi_if               )::set(null, "*.env.slv_agent" , "vif"            , slv_if        );
      
      // Run test
      uvm_top.enable_print_topology = 1;
      uvm_top.finish_on_completion  = 1;
      uvm_top.run_test();
   end
   
endmodule : uvmt_obi_st_tb


`endif // __UVMT_OBI_ST_TB_SV__
