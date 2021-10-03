// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// Copyright 2021 Silicon Labs
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef __UVMA_OBI_CFG_SV__
`define __UVMA_OBI_CFG_SV__


// Default sequences
typedef class uvma_obi_mon_vseq_c ;
typedef class uvma_obi_idle_vseq_c;
typedef class uvma_obi_mstr_vseq_c;
typedef class uvma_obi_slv_vseq_c ;


/**
 * Object encapsulating all parameters for creating, connecting and running all Open Bus Interface agent
 * (uvma_obi_agent_c) components.
 */
class uvma_obi_cfg_c extends uvm_object;
   
   // Generic options
   rand bit                      enabled          ; ///< TODO Describe uvma_obi_cfg_c::enabled
   rand uvm_active_passive_enum  is_active        ; ///< TODO Describe uvma_obi_cfg_c::is_active
   rand uvml_reset_mode_enum     reset_mode       ; ///< TODO Describe uvma_obi_cfg_c::reset_mode
   rand uvm_sequencer_arb_mode   sqr_arb_mode     ; ///< TODO Describe uvma_obi_cfg_c::sqr_arb_mode
   rand bit                      cov_model_enabled; ///< TODO Describe uvma_obi_cfg_c::cov_model_enabled
   rand bit                      trn_log_enabled  ; ///< TODO Describe uvma_obi_cfg_c::trn_log_enabled
   
   // Protocol Options
   rand uvma_obi_version_enum   version    ; ///< TODO Describe uvma_obi_cfg_c::version
   rand uvma_obi_mode_enum      drv_mode   ; ///< TODO Describe uvma_obi_cfg_c::drv_mode
   rand uvma_obi_drv_idle_enum  drv_idle   ; ///< TODO Describe uvma_obi_cfg_c::drv_idle
   rand int unsigned            auser_width; ///< TODO Describe uvma_obi_cfg_c::auser_width
   rand int unsigned            wuser_width; ///< TODO Describe uvma_obi_cfg_c::wuser_width
   rand int unsigned            ruser_width; ///< TODO Describe uvma_obi_cfg_c::ruser_width
   rand int unsigned            achk_width ; ///< TODO Describe uvma_obi_cfg_c::achk_width
   rand int unsigned            rchk_width ; ///< TODO Describe uvma_obi_cfg_c::rchk_width
   rand int unsigned            addr_width ; ///< TODO Describe uvma_obi_cfg_c::addr_width
   rand int unsigned            data_width ; ///< TODO Describe uvma_obi_cfg_c::data_width
   rand int unsigned            id_width   ; ///< TODO Describe uvma_obi_cfg_c::id_width
   
   // Sequence Types
   uvm_object_wrapper  monitor_vseq_type; ///< TODO Describe uvma_obi_cfg_c::monitor_vseq_type
   uvm_object_wrapper  idle_vseq_type   ; ///< TODO Describe uvma_obi_cfg_c::idle_vseq_type
   uvm_object_wrapper  mstr_vseq_type   ; ///< TODO Describe uvma_obi_cfg_c::mstr_vseq_type
   uvm_object_wrapper  slv_vseq_type    ; ///< TODO Describe uvma_obi_cfg_c::slv_vseq_type
   
   
   `uvm_object_utils_begin(uvma_obi_cfg_c)
      `uvm_field_int (                         enabled          , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active        , UVM_DEFAULT)
      `uvm_field_enum(uvml_reset_mode_enum   , reset_mode       , UVM_DEFAULT)
      `uvm_field_enum(uvm_sequencer_arb_mode , sqr_arb_mode     , UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled, UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled  , UVM_DEFAULT)
      
      `uvm_field_enum(uvma_obi_version_enum , version    , UVM_DEFAULT          )
      `uvm_field_enum(uvma_obi_mode_enum    , drv_mode   , UVM_DEFAULT          )
      `uvm_field_enum(uvma_obi_drv_idle_enum, drv_idle   , UVM_DEFAULT          )
      `uvm_field_int (                        auser_width, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        wuser_width, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        ruser_width, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        achk_width , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        rchk_width , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        addr_width , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        data_width , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (                        id_width   , UVM_DEFAULT + UVM_DEC)
   `uvm_object_utils_end
   
   
   constraint defaults_cons {
      soft enabled           == 1;
      soft is_active         == UVM_PASSIVE;
      soft reset_mode        == UVML_RESET_MODE_SYNCHRONOUS;
      soft sqr_arb_mode      == UVM_SEQ_ARB_FIFO;
      soft cov_model_enabled == 0;
      soft trn_log_enabled   == 1;
      
      soft version     == UVMA_OBI_VERSION_1P1;
      soft drv_idle    == UVMA_OBI_DRV_IDLE_ZEROS;
      soft auser_width == uvma_obi_default_auser_width;
      soft wuser_width == uvma_obi_default_wuser_width;
      soft ruser_width == uvma_obi_default_ruser_width;
      soft addr_width  == uvma_obi_default_addr_width ;
      soft data_width  == uvma_obi_default_data_width ;
      soft id_width    == uvma_obi_default_id_width   ;
      soft achk_width  == uvma_obi_default_achk_width ;
      soft rchk_width  == uvma_obi_default_rchk_width ;
   }
   
   constraint limits_cons {
      auser_width inside {[1:`UVMA_OBI_AUSER_MAX_WIDTH]};
      wuser_width inside {[1:`UVMA_OBI_WUSER_MAX_WIDTH]};
      ruser_width inside {[1:`UVMA_OBI_RUSER_MAX_WIDTH]};
      addr_width  inside {[1:`UVMA_OBI_ADDR_MAX_WIDTH ]};
      data_width  inside {[1:`UVMA_OBI_DATA_MAX_WIDTH ]};
      id_width    inside {[1:`UVMA_OBI_ID_MAX_WIDTH   ]};
      achk_width  inside {[1:`UVMA_OBI_ACHK_MAX_WIDTH ]};
      rchk_width  inside {[1:`UVMA_OBI_RCHK_MAX_WIDTH ]};
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_cfg");
   
endclass : uvma_obi_cfg_c


function uvma_obi_cfg_c::new(string name="uvma_obi_cfg");
   
   super.new(name);
   monitor_vseq_type = uvma_obi_mon_vseq_c ::type_id;
   idle_vseq_type    = uvma_obi_idle_vseq_c::type_id;
   mstr_vseq_type    = uvma_obi_mstr_vseq_c::type_id;
   slv_vseq_type     = uvma_obi_slv_vseq_c ::type_id;
   
endfunction : new


`endif // __UVMA_OBI_CFG_SV__
