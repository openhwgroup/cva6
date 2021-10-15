// Copyright 2021 OpenHW Group
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVMA_PMA_CFG_SV__
`define __UVMA_PMA_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all Memory attribution agent for OpenHW Group CORE-V verification testbenches agent (uvma_pma_agent_c) components.
 */
class uvma_pma_cfg_c#(int ILEN=DEFAULT_ILEN,
                      int XLEN=DEFAULT_XLEN) extends uvm_object;

   // Generic options
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand uvm_sequencer_arb_mode   sqr_arb_mode;
   rand bit                      scoreboard_enabled;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;

   // PMA regions
   uvma_core_cntrl_pma_region_c  regions[];

   `uvm_object_param_utils_begin(uvma_pma_cfg_c#(ILEN,XLEN))
      `uvm_field_int (                         enabled           , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active         , UVM_DEFAULT)
      `uvm_field_int (                         scoreboard_enabled, UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled , UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled   , UVM_DEFAULT)
      `uvm_field_array_object(                 regions           , UVM_DEFAULT)
   `uvm_object_utils_end


   constraint only_passive_cons {
      is_active              == UVM_PASSIVE;
   }

   constraint defaults_cons {
      soft enabled            == 1;
      soft cov_model_enabled  == 0;
      soft scoreboard_enabled == 1;
      soft trn_log_enabled    == 1;
   }


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_pma_cfg");

   /**
    * Return PMA region index for address, returns -1 if not mapped
    */
   extern virtual function int get_pma_region_for_addr(bit [XLEN-1:0] addr);

endclass : uvma_pma_cfg_c


function uvma_pma_cfg_c::new(string name="uvma_pma_cfg");

   super.new(name);

endfunction : new


function int uvma_pma_cfg_c::get_pma_region_for_addr(bit[XLEN-1:0] addr);

   // In default PMA configurations overlapping regions map from low index to high
   for (int i = 0; i < regions.size(); i++) begin
      if (regions[i].is_addr_in_region(addr))
         return i;
   end

   return -1;

endfunction : get_pma_region_for_addr


`endif // __UVMA_PMA_CFG_SV__
