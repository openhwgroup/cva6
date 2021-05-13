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


`ifndef __UVMA_OBI_CFG_SV__
`define __UVMA_OBI_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Open Bus Interface agent (uvma_obi_agent_c) components.
 */
class uvma_obi_cfg_c extends uvm_object;
   
   // Generic options
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand uvm_sequencer_arb_mode   sqr_arb_mode;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;
   
   // Protocol parameters
   rand int unsigned            auser_width;
   rand int unsigned            wuser_width;
   rand int unsigned            ruser_width;
   rand int unsigned            addr_width ;
   rand int unsigned            data_width ;
   rand int unsigned            id_width   ;
   rand uvma_obi_mode_enum      drv_mode   ;
   rand uvma_obi_drv_idle_enum  drv_idle   ;
   
   
   `uvm_object_utils_begin(uvma_obi_cfg_c)
      `uvm_field_int (                         enabled          , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active        , UVM_DEFAULT)
      `uvm_field_enum(uvm_sequencer_arb_mode , sqr_arb_mode     , UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled, UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled  , UVM_DEFAULT)
      
      `uvm_field_int (                        auser_width, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        wuser_width, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        ruser_width, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        auser_width, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        addr_width , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        data_width , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        id_width   , UVM_DEFAULT + UVM_DEC)
      `uvm_field_enum(uvma_obi_mode_enum    , drv_mode   , UVM_DEFAULT          )
      `uvm_field_enum(uvma_obi_drv_idle_enum, drv_idle   , UVM_DEFAULT          )
   `uvm_object_utils_end
   
   
   constraint defaults_cons {
      soft enabled           == 1;
      soft is_active         == UVM_PASSIVE;
      soft sqr_arb_mode      == UVM_SEQ_ARB_FIFO;
      soft cov_model_enabled == 0;
      soft trn_log_enabled   == 1;
      
      /*soft*/ auser_width  == uvma_obi_default_auser_width;
      /*soft*/ wuser_width  == uvma_obi_default_wuser_width;
      /*soft*/ ruser_width  == uvma_obi_default_ruser_width;
      /*soft*/ addr_width   == uvma_obi_default_addr_width ;
      /*soft*/ data_width   == uvma_obi_default_data_width ;
      /*soft*/ id_width     == uvma_obi_default_id_width   ;
      soft drv_mode     == UVMA_OBI_MODE_MSTR;
      soft drv_idle     == UVMA_OBI_DRV_IDLE_ZEROS;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_cfg");
   
endclass : uvma_obi_cfg_c


function uvma_obi_cfg_c::new(string name="uvma_obi_cfg");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_OBI_CFG_SV__
