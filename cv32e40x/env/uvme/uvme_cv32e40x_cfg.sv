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
class uvme_cv32e40x_cfg_c extends uvma_core_cntrl_cfg_c;

   // Integrals   
   rand int unsigned                sys_clk_period;

   // Agent cfg handles
   rand uvma_isacov_cfg_c           isacov_cfg;
   rand uvma_clknrst_cfg_c          clknrst_cfg;
   rand uvma_interrupt_cfg_c        interrupt_cfg;
   rand uvma_debug_cfg_c            debug_cfg;
   rand uvma_obi_cfg_c              obi_instr_cfg;
   rand uvma_obi_cfg_c              obi_data_cfg;
   rand uvma_rvfi_cfg_c#(ILEN,XLEN) rvfi_cfg;
   rand uvma_rvvi_cfg_c#(ILEN,XLEN) rvvi_cfg;
   
   `uvm_object_utils_begin(uvme_cv32e40x_cfg_c)
      `uvm_field_int (                         enabled                     , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active                   , UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled           , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled             , UVM_DEFAULT          )
      `uvm_field_int (                         sys_clk_period              , UVM_DEFAULT | UVM_DEC)            

      `uvm_field_object(isacov_cfg    , UVM_DEFAULT)
      `uvm_field_object(clknrst_cfg   , UVM_DEFAULT)
      `uvm_field_object(interrupt_cfg , UVM_DEFAULT)
      `uvm_field_object(debug_cfg     , UVM_DEFAULT)
      `uvm_field_object(obi_instr_cfg , UVM_DEFAULT)
      `uvm_field_object(obi_data_cfg  , UVM_DEFAULT)
      `uvm_field_object(rvfi_cfg      , UVM_DEFAULT)
      `uvm_field_object(rvvi_cfg      , UVM_DEFAULT)
   `uvm_object_utils_end
      
   constraint defaults_cons {
      soft enabled                == 0;
      soft is_active              == UVM_PASSIVE;
      soft scoreboarding_enabled  == 1; 
      soft cov_model_enabled      == 1;
      soft trn_log_enabled        == 1;
      soft sys_clk_period         == uvme_cv32e40x_sys_default_clk_period; // see uvme_cv32e40x_constants.sv      
   }

   constraint cv32e40x_riscv_cons {
      xlen == uvma_core_cntrl_pkg::MXL_32;
      ilen == 32;

      ext_i_supported        == 1;
      ext_c_supported        == 1;
      ext_m_supported        == 1;
      ext_zifencei_supported == 1;
      ext_zicsr_supported   == 1;

      ext_a_supported == 0;
      ext_p_supported == 0;
      ext_b_supported == 0;
      ext_v_supported == 0;
      ext_f_supported == 0;
      ext_d_supported == 0;
      
      mode_s_supported == 0;
      mode_u_supported == 0;
      pmp_supported == 0;
      debug_supported == 1;

      unaligned_access_supported == 1;
      unaligned_access_amo_supported == 1;

      boot_addr_valid         == 1;
      mtvec_addr_valid        == 1;
      dm_halt_addr_valid      == 1;
      dm_exception_addr_valid == 1;
      nmi_addr_valid          == 1;
   }

   constraint default_cv32e40x_boot_cons {
      (!hart_id_plusarg_valid)           -> (hart_id           == 'h0000_0000);
      (!boot_addr_plusarg_valid)         -> (boot_addr         == 'h0000_0080);
      (!mtvec_addr_plusarg_valid)        -> (mtvec_addr        == 'h0000_0000);
      (!nmi_addr_plusarg_valid)          -> (nmi_addr          == 'h2000_0000);
      (!dm_halt_addr_plusarg_valid)      -> (dm_halt_addr      == 'h1a11_0800);
      (!dm_exception_addr_plusarg_valid) -> (dm_exception_addr == 'h1a11_1000);
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
      isacov_cfg.seq_instr_group_x2_enabled == 1;
      isacov_cfg.seq_instr_group_x3_enabled == 1;
      isacov_cfg.seq_instr_group_x4_enabled == 0;
      isacov_cfg.reg_crosses_enabled        == 0;
      isacov_cfg.reg_hazards_enabled        == 1;

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
    * Run before randomizing this class
    */
   extern function void pre_randomize();

   /**
    * Run after randomizing this class
    */
   extern function void post_randomize();

   /**
    * Sample the parameters of the DUT via the virtual interface in a context
    */
   extern virtual function void sample_parameters(uvma_core_cntrl_cntxt_c cntxt);

   /**
    * Detect if a CSR check is disabled
    */
   extern virtual function bit is_csr_check_disabled(string name);


   /**
    * Configure CSR checks in the scoreboard
    */
   extern virtual function void configure_disable_csr_checks();

endclass : uvme_cv32e40x_cfg_c

function uvme_cv32e40x_cfg_c::new(string name="uvme_cv32e40x_cfg");
   
   super.new(name);

   if ($test$plusargs("USE_ISS")) 
      use_iss = 1;
   
   isacov_cfg = uvma_isacov_cfg_c::type_id::create("isacov_cfg");   
   clknrst_cfg  = uvma_clknrst_cfg_c::type_id::create("clknrst_cfg");
   interrupt_cfg = uvma_interrupt_cfg_c::type_id::create("interrupt_cfg");
   debug_cfg = uvma_debug_cfg_c    ::type_id::create("debug_cfg");
   obi_instr_cfg = uvma_obi_cfg_c::type_id::create("obi_instr_cfg");
   obi_data_cfg  = uvma_obi_cfg_c::type_id::create("obi_data_cfg");
   rvfi_cfg = uvma_rvfi_cfg_c#(ILEN,XLEN)::type_id::create("rvfi_cfg");
   rvvi_cfg = uvma_rvvi_ovpsim_cfg_c#(ILEN,XLEN)::type_id::create("rvvi_cfg");

   isacov_cfg.core_cfg = this;
   rvfi_cfg.core_cfg = this;
   rvvi_cfg.core_cfg = this;

endfunction : new

function void uvme_cv32e40x_cfg_c::pre_randomize();

   `uvm_info("CFG", $sformatf("Pre-randomize num_mhpmcounters = %0d", num_mhpmcounters), UVM_LOW);

endfunction : pre_randomize

function void uvme_cv32e40x_cfg_c::post_randomize();

   super.post_randomize();

   rvfi_cfg.instr_name[0] = "INSTR";

   // Set volatile locations for virtual peripherals
   rvvi_cfg.add_volatile_mem_addr_range(32'h1500_1000, 32'h1500_1007);
   rvvi_cfg.add_volatile_mem_addr_range(32'h1600_0000, 32'h1600_0fff);

   // Disable some CSR checks from all tests
   configure_disable_csr_checks();
   
endfunction : post_randomize

function void uvme_cv32e40x_cfg_c::sample_parameters(uvma_core_cntrl_cntxt_c cntxt);

   uvma_cv32e40x_core_cntrl_cntxt_c e40x_cntxt;

   if (!$cast(e40x_cntxt, cntxt)) begin
      `uvm_fatal("SAMPLECNTXT", "Could not cast cntxt to uvma_cv32e40x_core_cntrl_cntxt_c");
   end

   num_mhpmcounters = e40x_cntxt.core_cntrl_vif.num_mhpmcounters;
   pma_regions      = new[e40x_cntxt.core_cntrl_vif.pma_cfg.size()];
   foreach (pma_regions[i]) begin
      pma_regions[i] = uvma_core_cntrl_pma_region_c::type_id::create($sformatf("pma_region%0d", i));
      pma_regions[i].word_addr_low  = e40x_cntxt.core_cntrl_vif.pma_cfg[i].word_addr_low;
      pma_regions[i].word_addr_high = e40x_cntxt.core_cntrl_vif.pma_cfg[i].word_addr_high;
      pma_regions[i].main           = e40x_cntxt.core_cntrl_vif.pma_cfg[i].main;
      pma_regions[i].bufferable     = e40x_cntxt.core_cntrl_vif.pma_cfg[i].bufferable;
      pma_regions[i].cacheable      = e40x_cntxt.core_cntrl_vif.pma_cfg[i].cacheable;
      pma_regions[i].atomic         = e40x_cntxt.core_cntrl_vif.pma_cfg[i].atomic;
   end

endfunction : sample_parameters

function bit uvme_cv32e40x_cfg_c::is_csr_check_disabled(string name);

   // Fatal error if passed a CSR check which is non-existent
   if (!csr_name2addr.exists(name)) begin
      `uvm_fatal("CV32E40XCFG", $sformatf("CSR [%s] does not exist", name));
   end

   return disable_csr_check_mask[csr_name2addr[name]];

endfunction : is_csr_check_disabled

function void uvme_cv32e40x_cfg_c::configure_disable_csr_checks();

   // Need to check
   disable_csr_check("mcountinhibit");

   // Not possible to test on a cycle-by-cycle basis
   disable_csr_check("mip");

   // These are not implemented in the ISS
   disable_csr_check("mcycle");
   disable_csr_check("mcycleh");
   disable_csr_check("mtval");

   for (int i = 3; i < 32; i++) begin
      disable_csr_check($sformatf("mhpmcounter%0d", i));
      disable_csr_check($sformatf("mhpmcounter%0dh", i));
      disable_csr_check($sformatf("mhpmevent%0d", i));      
   end
endfunction : configure_disable_csr_checks


`endif // __UVME_CV32E40X_CFG_SV__


