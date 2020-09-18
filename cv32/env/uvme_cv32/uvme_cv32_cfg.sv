// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVME_CV32_CFG_SV__
`define __UVME_CV32_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * CV32 environment (uvme_cv32_env_c) components.
 */
class uvme_cv32_cfg_c extends uvm_object;
   
   // Integrals
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand bit                      scoreboarding_enabled;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;
   rand int unsigned             sys_clk_period;
   //rand int unsigned             debug_clk_period;
   
   // Agent cfg handles
   rand uvma_clknrst_cfg_c    clknrst_cfg;
   rand uvma_interrupt_cfg_c  interrupt_cfg;
   rand uvma_debug_cfg_c    debug_cfg;
   
   // Objects
   rand uvme_cv32_ral_c  ral;
   // TODO Add scoreboard configuration handles
   //      Ex: rand uvml_sb_cfg_c  sb_egress_cfg;
   //          rand uvml_sb_cfg_c  sb_ingress_cfg;
   
   
   `uvm_object_utils_begin(uvme_cv32_cfg_c)
      `uvm_field_int (                         enabled                     , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active                   , UVM_DEFAULT          )
      `uvm_field_int (                         scoreboarding_enabled       , UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled           , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled             , UVM_DEFAULT          )
      `uvm_field_int (                         sys_clk_period            , UVM_DEFAULT + UVM_DEC)
      //`uvm_field_int (                         debug_clk_period            , UVM_DEFAULT + UVM_DEC)
      
      `uvm_field_object(clknrst_cfg, UVM_DEFAULT)
      `uvm_field_object(interrupt_cfg, UVM_DEFAULT)
      `uvm_field_object(debug_cfg  , UVM_DEFAULT)
      
      //`uvm_field_object(ral, UVM_DEFAULT)
      // TODO Add scoreboard cfg field macros
      //      Ex: `uvm_field_object(sb_egress_cfg , UVM_DEFAULT)
      //          `uvm_field_object(sb_ingress_cfg, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   constraint defaults_cons {
      soft enabled                == 0;
      soft is_active              == UVM_PASSIVE;
      soft scoreboarding_enabled  == 1;      
      soft cov_model_enabled      == 1;
      soft trn_log_enabled        == 1;
      soft sys_clk_period       == uvme_cv32_sys_default_clk_period; // see uvme_cv32_constants.sv
      //soft debug_clk_period       == uvme_cv32_debug_default_clk_period;
   }
   
   constraint agent_cfg_cons {
      if (enabled) {
         clknrst_cfg.enabled == 1;
         interrupt_cfg.enabled == 1;
         debug_cfg.enabled == 1;
      }
      
      if (is_active == UVM_ACTIVE) {
         clknrst_cfg.is_active == UVM_ACTIVE;
         interrupt_cfg.is_active == UVM_ACTIVE;
         debug_cfg.is_active == UVM_ACTIVE;
      }
      
      if (trn_log_enabled) {
         clknrst_cfg.trn_log_enabled == 1;
         interrupt_cfg.trn_log_enabled == 1;
         debug_cfg.trn_log_enabled == 1;
      }
   }   
   
   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvme_cv32_cfg");
   
endclass : uvme_cv32_cfg_c


function uvme_cv32_cfg_c::new(string name="uvme_cv32_cfg");
   
   super.new(name);
   
   clknrst_cfg = uvma_clknrst_cfg_c::type_id::create("clknrst_cfg");
   interrupt_cfg = uvma_interrupt_cfg_c::type_id::create("interrupt_cfg");
   debug_cfg = uvma_debug_cfg_c    ::type_id::create("debug_cfg");
   
   ral = uvme_cv32_ral_c::type_id::create("ral");
   ral.build();
   ral.lock_model();
   
   // TODO Create scoreboard cfg objects
   //      Ex: sb_egress_cfg  = uvml_sb_cfg_c::type_id::create("sb_egress_cfg" );
   //          sb_ingress_cfg = uvml_sb_cfg_c::type_id::create("sb_ingress_cfg");
   
endfunction : new


`endif // __UVME_CV32_CFG_SV__
