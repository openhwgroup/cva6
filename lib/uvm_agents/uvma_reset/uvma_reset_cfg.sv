// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


`ifndef __UVMA_RESET_CFG_SV__
`define __UVMA_RESET_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Reset agent (uvma_reset_agent_c) components.
 */
class uvma_reset_cfg_c extends uvm_object;
   
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand uvm_sequencer_arb_mode   sqr_arb_mode;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;
   
   
   `uvm_object_utils_begin(uvma_reset_cfg_c)
      `uvm_field_int (                         enabled          , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active        , UVM_DEFAULT)
      `uvm_field_enum(uvm_sequencer_arb_mode , sqr_arb_mode     , UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled, UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled  , UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   constraint defaults_cons {
      soft enabled           == 1;
      soft is_active         == UVM_PASSIVE;
      soft sqr_arb_mode      == UVM_SEQ_ARB_FIFO;
      soft cov_model_enabled == 0;
      soft trn_log_enabled   == 1;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_reset_cfg");
   
endclass : uvma_reset_cfg_c


`pragma protect begin


function uvma_reset_cfg_c::new(string name="uvma_reset_cfg");
   
   super.new(name);
   
endfunction : new


`pragma protect end


`endif // __UVMA_RESET_CFG_SV__
