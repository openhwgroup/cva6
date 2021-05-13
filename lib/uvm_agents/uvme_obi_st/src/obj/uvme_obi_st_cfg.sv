// 
// Copyright 2021 OpenHW Group
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


`ifndef __UVME_OBI_ST_CFG_SV__
`define __UVME_OBI_ST_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * Open Bus Interface VIP Self-Testing Environment (uvme_obi_st_env_c)
 * components.
 */
class uvme_obi_st_cfg_c extends uvm_object;
   
   // Integrals
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand bit                      scoreboarding_enabled;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;
   
   // Objects
   rand uvma_obi_cfg_c  mstr_cfg;
   rand uvma_obi_cfg_c  slv_cfg;
   rand uvml_sb_cfg_c   sb_cfg;
   
   
   `uvm_object_utils_begin(uvme_obi_st_cfg_c)
      `uvm_field_int (                         enabled              , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active            , UVM_DEFAULT)
      `uvm_field_int (                         scoreboarding_enabled, UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled    , UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled      , UVM_DEFAULT)
      
      `uvm_field_object(mstr_cfg, UVM_DEFAULT)
      `uvm_field_object(slv_cfg , UVM_DEFAULT)
      `uvm_field_object(sb_cfg  , UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   constraint defaults_cons {
      soft enabled                == 0;
      soft is_active              == UVM_PASSIVE;
      soft scoreboarding_enabled  == 1;
      soft cov_model_enabled      == 0;
      soft trn_log_enabled        == 1;
   }
   
   constraint agents_generic_cfg_cons {
      if (enabled) {
         mstr_cfg.enabled == 1;
         slv_cfg .enabled == 1;
      }
      else {
         mstr_cfg.enabled == 0;
         slv_cfg .enabled == 0;
      }
      
      if (is_active == UVM_ACTIVE) {
         mstr_cfg.is_active == UVM_ACTIVE;
         slv_cfg .is_active == UVM_ACTIVE;
      }
      else {
         mstr_cfg.is_active == UVM_PASSIVE;
         slv_cfg .is_active == UVM_PASSIVE;
      }
      
      if (trn_log_enabled) {
         /*soft*/ mstr_cfg.trn_log_enabled == 1;
         /*soft*/ slv_cfg .trn_log_enabled == 1;
      }
      else {
         /*soft*/ mstr_cfg.trn_log_enabled == 0;
         /*soft*/ slv_cfg .trn_log_enabled == 0;
      }
   }
   
   constraint agents_protocol_cons {
      mstr_cfg.auser_width == slv_cfg.auser_width;
      mstr_cfg.wuser_width == slv_cfg.wuser_width;
      mstr_cfg.ruser_width == slv_cfg.ruser_width;
      mstr_cfg.addr_width  == slv_cfg.addr_width ;
      mstr_cfg.data_width  == slv_cfg.data_width ;
      mstr_cfg.id_width    == slv_cfg.id_width   ;
      
      mstr_cfg.drv_mode == UVMA_OBI_MODE_MSTR ;
      mstr_cfg.drv_idle == UVMA_OBI_DRV_IDLE_X;
      slv_cfg .drv_mode == UVMA_OBI_MODE_SLV  ;
      slv_cfg .drv_idle == UVMA_OBI_DRV_IDLE_X;
   }
   
   constraint sb_cfg_cons {
      if (scoreboarding_enabled) {
         /*soft*/ sb_cfg.enabled == 1;
         sb_cfg.mode == UVML_SB_MODE_IN_ORDER;
      }
      else {
         sb_cfg.enabled == 0;
      }
   }
   
   
   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvme_obi_st_cfg");
   
endclass : uvme_obi_st_cfg_c


function uvme_obi_st_cfg_c::new(string name="uvme_obi_st_cfg");
   
   super.new(name);
   
   mstr_cfg = uvma_obi_cfg_c::type_id::create("mstr_cfg");
   slv_cfg  = uvma_obi_cfg_c::type_id::create("slv_cfg" );
   sb_cfg   = uvml_sb_cfg_c ::type_id::create("sb_cfg"  );
   
endfunction : new


`endif // __UVME_OBI_ST_CFG_SV__
