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


`ifndef __UVME_CV32E40X_CFG_SV__
`define __UVME_CV32E40X_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * CV32E40X environment (uvme_cv32e40x_env_c) components.
 */
class uvme_cv32e40x_cfg_c extends uvm_object;

   // Status of plusarg to control testbench features
   bit                           use_iss  = 0;
   bit                           use_rvvi = 0;   

   // Integrals
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   bit                           use_isacov;

   rand bit                      scoreboarding_enabled;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;
   rand int unsigned             sys_clk_period;
   
   // Agent cfg handles
   rand uvma_isacov_cfg_c     isacov_cfg;
   rand uvma_clknrst_cfg_c    clknrst_cfg;
   rand uvma_interrupt_cfg_c  interrupt_cfg;
   rand uvma_debug_cfg_c      debug_cfg;
   rand uvma_obi_cfg_c        obi_instr_cfg;
   rand uvma_obi_cfg_c        obi_data_cfg;
   rand uvma_rvfi_cfg_c#(ILEN,XLEN) rvfi_cfg;
   rand uvma_rvvi_cfg_c#(ILEN,XLEN) rvvi_cfg;
   
   
   `uvm_object_utils_begin(uvme_cv32e40x_cfg_c)
      `uvm_field_int (                         enabled                     , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active                   , UVM_DEFAULT          )
      `uvm_field_int (                         scoreboarding_enabled       , UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled           , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled             , UVM_DEFAULT          )
      `uvm_field_int (                         sys_clk_period            , UVM_DEFAULT + UVM_DEC)      
      
      `uvm_field_object(isacov_cfg, UVM_DEFAULT)
      `uvm_field_object(clknrst_cfg, UVM_DEFAULT)
      `uvm_field_object(interrupt_cfg, UVM_DEFAULT)
      `uvm_field_object(debug_cfg  , UVM_DEFAULT)
      `uvm_field_object(obi_instr_cfg, UVM_DEFAULT)
      `uvm_field_object(obi_data_cfg, UVM_DEFAULT)
      `uvm_field_object(rvfi_cfg, UVM_DEFAULT)
      `uvm_field_object(rvvi_cfg, UVM_DEFAULT)
   `uvm_object_utils_end
      
   constraint defaults_cons {
      soft enabled                == 0;
      soft is_active              == UVM_PASSIVE;
      soft scoreboarding_enabled  == 1; 
      soft cov_model_enabled      == 1;
      soft trn_log_enabled        == 1;
      soft sys_clk_period         == uvme_cv32e40x_sys_default_clk_period; // see uvme_cv32e40x_constants.sv      
   }
   
   constraint scoreboard_cons {
      (!(use_iss && use_rvvi)) -> (scoreboarding_enabled == 0);
   }
   constraint agent_cfg_cons {
      if (enabled) {
         clknrst_cfg.enabled   == 1;
         interrupt_cfg.enabled == 1;
         debug_cfg.enabled     == 1;
         obi_instr_cfg.enabled == 1;
         obi_data_cfg.enabled  == 1;
         rvfi_cfg.enabled      == 1;
         rvvi_cfg.enabled      == 1;
      }
      obi_instr_cfg.write_enabled == 0;
      obi_instr_cfg.read_enabled  == 1;
      obi_data_cfg.write_enabled  == 1;
      obi_data_cfg.read_enabled   == 1;

      isacov_cfg.enabled                    == use_isacov;  // TODO don't need "== 0" after uvma_isacov has matured enough
      isacov_cfg.ext_i_enabled              == 1;
      isacov_cfg.ext_m_enabled              == 1;
      isacov_cfg.ext_c_enabled              == 1;
      isacov_cfg.ext_a_enabled              == 0;
      isacov_cfg.ext_zifencei_enabled       == 1;
      isacov_cfg.ext_zicsr_enabled          == 1;
      isacov_cfg.mode_u_enabled             == 0;
      isacov_cfg.mode_s_enabled             == 0;
      isacov_cfg.seq_instr_group_x2_enabled == 1;
      isacov_cfg.seq_instr_group_x3_enabled == 1;
      isacov_cfg.seq_instr_group_x4_enabled == 0;
      isacov_cfg.reg_crosses_enabled        == 0;

      rvfi_cfg.nret == uvme_cv32e40x_pkg::RVFI_NRET;
      rvfi_cfg.nmi_handler_enabled        == 0; // FIXME:strichmo:implement when NMI implemented in e40x
      rvfi_cfg.debug_halt_handler_enabled == 1;

      if (is_active == UVM_ACTIVE) {
         isacov_cfg.is_active    == UVM_PASSIVE;
         clknrst_cfg.is_active   == UVM_ACTIVE;
         interrupt_cfg.is_active == UVM_ACTIVE;
         debug_cfg.is_active     == UVM_ACTIVE;
         obi_instr_cfg.is_active == UVM_PASSIVE;
         obi_data_cfg.is_active  == UVM_PASSIVE;
         rvfi_cfg.is_active      == UVM_PASSIVE;
         (use_rvvi) -> rvvi_cfg.is_active == UVM_ACTIVE;
         (!use_rvvi)-> rvvi_cfg.is_active == UVM_PASSIVE;
      }
      
      if (trn_log_enabled) {
         isacov_cfg.trn_log_enabled    == 1;
         clknrst_cfg.trn_log_enabled   == 1;
         interrupt_cfg.trn_log_enabled == 1;
         debug_cfg.trn_log_enabled     == 1;
         obi_instr_cfg.trn_log_enabled == 1;
         obi_data_cfg.trn_log_enabled  == 1;
         rvfi_cfg.trn_log_enabled      == 1;
         rvvi_cfg.trn_log_enabled      == 1;
      }

      if (cov_model_enabled) {
         isacov_cfg.cov_model_enabled    == 1;
         obi_instr_cfg.cov_model_enabled == 1;
         obi_data_cfg.cov_model_enabled  == 1;
      }
   }   
   
   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvme_cv32e40x_cfg");
   /**
    * Run after randomizing this class
    */
   extern function void post_randomize();

endclass : uvme_cv32e40x_cfg_c


function uvme_cv32e40x_cfg_c::new(string name="uvme_cv32e40x_cfg");
   
   super.new(name);

   if ($test$plusargs("USE_ISS")) 
      use_iss = 1;

   if ($test$plusargs("USE_RVVI")) 
      use_rvvi = 1;
      
   isacov_cfg = uvma_isacov_cfg_c::type_id::create("isacov_cfg");
   clknrst_cfg  = uvma_clknrst_cfg_c::type_id::create("clknrst_cfg");
   interrupt_cfg = uvma_interrupt_cfg_c::type_id::create("interrupt_cfg");
   debug_cfg = uvma_debug_cfg_c    ::type_id::create("debug_cfg");
   obi_instr_cfg = uvma_obi_cfg_c::type_id::create("obi_instr_cfg");
   obi_data_cfg  = uvma_obi_cfg_c::type_id::create("obi_data_cfg");
   rvfi_cfg = uvma_rvfi_cfg_c#(ILEN,XLEN)::type_id::create("rvfi_cfg");
   rvvi_cfg = uvma_rvvi_ovpsim_cfg_c#(ILEN,XLEN)::type_id::create("rvvi_cfg");
endfunction : new

function void uvme_cv32e40x_cfg_c::post_randomize();
   rvfi_cfg.instr_name[0] = "INSTR";
endfunction : post_randomize

`endif // __UVME_CV32E40X_CFG_SV__

