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


`ifndef __UVME_COREV_CORE_CFG_SV__
`define __UVME_COREV_CORE_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * A CORE-V core
 * Core environments should inherit from this class defintion to create their 
 * specific core implementation
 */
virtual class uvme_corev_core_cfg_c extends uvm_object;

   // Major mode enable controls
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;      
   
   // RISC-V ISA Configuration
   rand corev_mxl_t              xlen;
   rand int unsigned             ilen;

   rand bit                      ext_i_supported;
   rand bit                      ext_a_supported;
   rand bit                      ext_m_supported;
   rand bit                      ext_c_supported;
   rand bit                      ext_b_supported;
   rand bit                      ext_p_supported;
   rand bit                      ext_zifencei_supported;
   rand bit                      ext_zicsri_supported;

   rand bit                      mode_s_supported;
   rand bit                      mode_u_supported;

   rand bit                      debug_supported;

   rand bit                      unaligned_access_supported;
   rand bit                      unaligned_access_amo_supported;

   // Memory map
   rand bit [MAX_XLEN-1:0]       boot_addr;
   rand bit [MAX_XLEN-1:0]       mtvec_addr;
   rand bit [MAX_XLEN-1:0]       mtvec_writable_mask;
   rand bit [MAX_XLEN-1:0]       nmi_addr;
   rand bit                      nmi_valid;
   rand bit                      nmi_valid;


   `uvm_field_utils_begin(uvme_corev_core_cfg_c);
      `uvm_field_int (                         enabled                     , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active                   , UVM_DEFAULT          )
      `uvm_field_int (                         scoreboarding_enabled       , UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled           , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled             , UVM_DEFAULT          )
      `uvm_field_enum(corev_mxl_t              xlen                        , UVM_DEFAULT          )
      `uvm_field_int (                         ilen                        , UVM_DEFAULT          )
      
   `uvm_field_utils_end
      
   constraint defaults_cons {
      soft enabled                == 0;
      soft is_active              == UVM_PASSIVE;
      soft cov_model_enabled      == 1;
      soft trn_log_enabled        == 1;
   }
   
   constraint scoreboard_cons {
      (!use_iss) -> (scoreboarding_enabled == 0);      
   }

   constraint agent_cfg_cons {
      if (enabled) {
         clknrst_cfg.enabled   == 1;
         interrupt_cfg.enabled == 1;
         debug_cfg.enabled     == 1;
         obi_instr_cfg.enabled == 1;
         obi_data_cfg.enabled  == 1;
         rvfi_cfg.enabled      == 1;
         rvvi_cfg.enabled      == use_iss;
      }
      obi_instr_cfg.write_enabled == 0;
      obi_instr_cfg.read_enabled  == 1;
      obi_data_cfg.write_enabled  == 1;
      obi_data_cfg.read_enabled   == 1;

      isacov_cfg.enabled                    == 1;
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

      if (is_active == UVM_ACTIVE) {
         isacov_cfg.is_active    == UVM_PASSIVE;
         clknrst_cfg.is_active   == UVM_ACTIVE;
         interrupt_cfg.is_active == UVM_ACTIVE;
         debug_cfg.is_active     == UVM_ACTIVE;
         obi_instr_cfg.is_active == UVM_PASSIVE;
         obi_data_cfg.is_active  == UVM_PASSIVE;
         rvfi_cfg.is_active      == UVM_PASSIVE;
         rvvi_cfg.is_active      == UVM_ACTIVE;         
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

      // FIXME:strichmo:restore when debug coverage model is fixed
      debug_cfg.cov_model_enabled == 0;

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

   /**
    * Configure the CSRs to be checked in the RVFI/RVVI scoreboard
    * Could be overridden as necessary by specialized tests
    */
   extern virtual function void configure_csr_rvfi_checks();

endclass : uvme_cv32e40x_cfg_c

function uvme_cv32e40x_cfg_c::new(string name="uvme_cv32e40x_cfg");
   
   super.new(name);

   if ($test$plusargs("USE_ISS")) 
      use_iss = 1;
   
   if ($test$plusargs("disable_csr_chk")) 
      disable_csr_check = 1;

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

   // Set volatile locations for virtual peripherals
   rvvi_cfg.add_volatile_mem_addr_range(32'h1500_1000, 32'h1500_1007);
   rvvi_cfg.add_volatile_mem_addr_range(32'h1600_0000, 32'h1600_0fff);

   configure_csr_rvfi_checks();

endfunction : post_randomize

function void uvme_cv32e40x_cfg_c::configure_csr_rvfi_checks();

   // Configure the supported CSRs for checking in the CV32E40X
   rvfi_cfg.csrs.push_back("marchid");
   //rvfi_cfg.csrs.push_back("mcountinhibit");
   rvfi_cfg.csrs.push_back("mstatus");
   rvfi_cfg.csrs.push_back("misa");
   rvfi_cfg.csrs.push_back("mtvec");
   rvfi_cfg.csrs.push_back("mvendorid");
   rvfi_cfg.csrs.push_back("mscratch");
   //rvfi_cfg.csrs.push_back("mepc");
   rvfi_cfg.csrs.push_back("mcause");
   rvfi_cfg.csrs.push_back("mie");
   rvfi_cfg.csrs.push_back("mimpid");
   rvfi_cfg.csrs.push_back("minstret");
   rvfi_cfg.csrs.push_back("minstreth");
   //rvfi_cfg.csrs.push_back("mip");
   rvfi_cfg.csrs.push_back("mhartid");
   rvfi_cfg.csrs.push_back("mcontext");

   rvfi_cfg.csrs.push_back("dcsr");
   rvfi_cfg.csrs.push_back("dpc");
   rvfi_cfg.csrs.push_back("dscratch0");
   rvfi_cfg.csrs.push_back("dscratch1");
   rvfi_cfg.csrs.push_back("scontext");

   rvfi_cfg.csrs.push_back("tselect");   
   rvfi_cfg.csrs.push_back("tdata1");
   rvfi_cfg.csrs.push_back("tdata2");
   rvfi_cfg.csrs.push_back("tdata3");
   rvfi_cfg.csrs.push_back("tinfo");

endfunction : configure_csr_rvfi_checks

`endif // __UVME_CV32E40X_CFG_SV__

