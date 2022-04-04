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


`ifndef __UVME_CV32E40S_CFG_SV__
`define __UVME_CV32E40S_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * CV32E40S environment (uvme_cv32e40s_env_c) components.
 */
class uvme_cv32e40s_cfg_c extends uvma_core_cntrl_cfg_c;

   // Integrals
   rand int unsigned                sys_clk_period;
   cv32e40s_pkg::b_ext_e            b_ext;
   bit                              obi_memory_instr_random_err_enabled   = 0;
   bit                              obi_memory_instr_one_shot_err_enabled = 0;
   bit                              obi_memory_data_random_err_enabled    = 0;
   bit                              obi_memory_data_one_shot_err_enabled  = 0;
   rand bit                         buserr_scoreboarding_enabled          = 1;

   // Agent cfg handles
   rand uvma_isacov_cfg_c           isacov_cfg;
   rand uvma_clknrst_cfg_c          clknrst_cfg;
   rand uvma_interrupt_cfg_c        interrupt_cfg;
   rand uvma_debug_cfg_c            debug_cfg;
   rand uvma_obi_memory_cfg_c       obi_memory_instr_cfg;
   rand uvma_obi_memory_cfg_c       obi_memory_data_cfg;
   rand uvma_fencei_cfg_c           fencei_cfg;
   rand uvma_rvfi_cfg_c#(ILEN,XLEN) rvfi_cfg;
   rand uvma_rvvi_cfg_c#(ILEN,XLEN) rvvi_cfg;
   rand uvma_pma_cfg_c#(ILEN,XLEN)  pma_cfg;

   `uvm_object_utils_begin(uvme_cv32e40s_cfg_c)
      `uvm_field_int (                         enabled                     , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active                   , UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled           , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled             , UVM_DEFAULT          )
      `uvm_field_int (                         buserr_scoreboarding_enabled, UVM_DEFAULT          )
      `uvm_field_int (                         sys_clk_period              , UVM_DEFAULT | UVM_DEC)
      `uvm_field_enum (cv32e40s_pkg::b_ext_e,  b_ext                       , UVM_DEFAULT          )
      `uvm_field_int (                         obi_memory_instr_random_err_enabled,   UVM_DEFAULT  )
      `uvm_field_int (                         obi_memory_instr_one_shot_err_enabled, UVM_DEFAULT  )
      `uvm_field_int (                         obi_memory_data_random_err_enabled,    UVM_DEFAULT  )
      `uvm_field_int (                         obi_memory_data_one_shot_err_enabled,  UVM_DEFAULT  )

      `uvm_field_object(isacov_cfg           , UVM_DEFAULT)
      `uvm_field_object(clknrst_cfg          , UVM_DEFAULT)
      `uvm_field_object(interrupt_cfg        , UVM_DEFAULT)
      `uvm_field_object(debug_cfg            , UVM_DEFAULT)
      `uvm_field_object(obi_memory_instr_cfg , UVM_DEFAULT)
      `uvm_field_object(obi_memory_data_cfg  , UVM_DEFAULT)
      `uvm_field_object(rvfi_cfg             , UVM_DEFAULT)
      `uvm_field_object(rvvi_cfg             , UVM_DEFAULT)
      `uvm_field_object(fencei_cfg           , UVM_DEFAULT)
      `uvm_field_object(pma_cfg              , UVM_DEFAULT)
   `uvm_object_utils_end


   constraint defaults_cons {
      soft enabled                      == 0;
      soft is_active                    == UVM_PASSIVE;
      soft scoreboarding_enabled        == 1;
      soft cov_model_enabled            == 1;
      soft trn_log_enabled              == 1;
      soft sys_clk_period               == uvme_cv32e40s_sys_default_clk_period; // see uvme_cv32e40s_constants.sv
      soft buserr_scoreboarding_enabled == 1;
   }

   constraint cv32e40s_riscv_cons {
      xlen == uvma_core_cntrl_pkg::MXL_32;
      ilen == 32;

      ext_i_supported        == 1;
      ext_c_supported        == 1;
      ext_m_supported        == 1;
      ext_zifencei_supported == 1;
      ext_zicsr_supported    == 1;
      ext_a_supported        == 0;
      ext_p_supported        == 0;
      ext_v_supported        == 0;
      ext_f_supported        == 0;
      ext_d_supported        == 0;

      if (b_ext == cv32e40s_pkg::B_NONE) {
         ext_zba_supported == 0;
         ext_zbb_supported == 0;
         ext_zbc_supported == 0;
         ext_zbs_supported == 0;
      } else if (b_ext == cv32e40s_pkg::ZBA_ZBB_ZBS) {
         ext_zba_supported == 1;
         ext_zbb_supported == 1;
         ext_zbc_supported == 0;
         ext_zbs_supported == 1;
      } else if (b_ext == cv32e40s_pkg::ZBA_ZBB_ZBC_ZBS) {
         ext_zba_supported == 1;
         ext_zbb_supported == 1;
         ext_zbc_supported == 1;
         ext_zbs_supported == 1;
      }
      ext_zbe_supported == 0;
      ext_zbf_supported == 0;
      ext_zbm_supported == 0;
      ext_zbp_supported == 0;
      ext_zbr_supported == 0;
      ext_zbt_supported == 0;

      mode_s_supported == 0;
      mode_u_supported == 0;
      pmp_supported == 0;
      debug_supported == 1;

      unaligned_access_supported == 1;
      unaligned_access_amo_supported == 1;

      bitmanip_version        == BITMANIP_VERSION_1P00;
      priv_spec_version       == PRIV_VERSION_MASTER;
      endianness              == ENDIAN_LITTLE;

      boot_addr_valid         == 1;
      mtvec_addr_valid        == 1;
      dm_halt_addr_valid      == 1;
      dm_exception_addr_valid == 1;
      nmi_addr_valid          == 1;
   }

   constraint default_cv32e40s_boot_cons {
      (!mhartid_plusarg_valid)           -> (mhartid           == 'h0000_0000);
      (!mimpid_plusarg_valid)            -> (mimpid            == 'h0000_0000);
      (!boot_addr_plusarg_valid)         -> (boot_addr         == 'h0000_0080);
      (!mtvec_addr_plusarg_valid)        -> (mtvec_addr        == 'h0000_0000);
      (!nmi_addr_plusarg_valid)          -> (nmi_addr          == 'h0010_0000);
      (!dm_halt_addr_plusarg_valid)      -> (dm_halt_addr      == 'h1a11_0800);
      (!dm_exception_addr_plusarg_valid) -> (dm_exception_addr == 'h1a11_1000);
   }

   constraint agent_cfg_cons {
      if (enabled) {
         clknrst_cfg.enabled           == 1;
         interrupt_cfg.enabled         == 1;
         debug_cfg.enabled             == 1;
         rvfi_cfg.enabled              == 1;
         rvvi_cfg.enabled              == use_iss;
         obi_memory_instr_cfg.enabled  == 1;
         obi_memory_data_cfg.enabled   == 1;
         fencei_cfg.enabled            == 1;
      }

      obi_memory_instr_cfg.version       == UVMA_OBI_MEMORY_VERSION_1P2;
      obi_memory_instr_cfg.drv_mode      == UVMA_OBI_MEMORY_MODE_SLV;
      obi_memory_instr_cfg.write_enabled == 0;
      obi_memory_instr_cfg.addr_width    == XLEN;
      obi_memory_instr_cfg.data_width    == XLEN;
      obi_memory_instr_cfg.id_width      == 0;
      obi_memory_instr_cfg.achk_width    == 0;
      obi_memory_instr_cfg.rchk_width    == 0;
      obi_memory_instr_cfg.auser_width   == 0;
      obi_memory_instr_cfg.ruser_width   == 0;
      obi_memory_instr_cfg.wuser_width   == 0;
      soft obi_memory_instr_cfg.drv_slv_gnt_random_latency_max    <= 3;
      soft obi_memory_instr_cfg.drv_slv_rvalid_random_latency_max <= 6;

      obi_memory_data_cfg.version        == UVMA_OBI_MEMORY_VERSION_1P2;
      obi_memory_data_cfg.drv_mode       == UVMA_OBI_MEMORY_MODE_SLV;
      obi_memory_data_cfg.addr_width     == XLEN;
      obi_memory_data_cfg.data_width     == XLEN;
      obi_memory_data_cfg.id_width       == 0;
      obi_memory_data_cfg.achk_width     == 0;
      obi_memory_data_cfg.rchk_width     == 0;
      obi_memory_data_cfg.auser_width    == 0;
      obi_memory_data_cfg.ruser_width    == 0;
      obi_memory_data_cfg.wuser_width    == 0;
      soft obi_memory_data_cfg.drv_slv_gnt_random_latency_max    <= 3;
      soft obi_memory_data_cfg.drv_slv_rvalid_random_latency_max <= 6;

      isacov_cfg.enabled                    == 1;
      isacov_cfg.seq_instr_group_x2_enabled == 1;
      isacov_cfg.seq_instr_group_x3_enabled == 1;
      isacov_cfg.seq_instr_group_x4_enabled == 0;
      isacov_cfg.seq_instr_x2_enabled       == 1;
      isacov_cfg.reg_crosses_enabled        == 0;
      isacov_cfg.reg_hazards_enabled        == 1;

      rvfi_cfg.nret == uvme_cv32e40s_pkg::RVFI_NRET;
      rvfi_cfg.nmi_load_fault_enabled      == 1;
      rvfi_cfg.nmi_load_fault_cause        == cv32e40s_pkg::INT_CAUSE_LSU_LOAD_FAULT;
      rvfi_cfg.nmi_store_fault_enabled     == 1;
      rvfi_cfg.nmi_store_fault_cause       == cv32e40s_pkg::INT_CAUSE_LSU_STORE_FAULT;
      rvfi_cfg.insn_bus_fault_enabled      == 1;
      rvfi_cfg.insn_bus_fault_cause        == cv32e40s_pkg::EXC_CAUSE_INSTR_BUS_FAULT;

      if (is_active == UVM_ACTIVE) {
         isacov_cfg.is_active           == UVM_PASSIVE;
         clknrst_cfg.is_active          == UVM_ACTIVE;
         interrupt_cfg.is_active        == UVM_ACTIVE;
         debug_cfg.is_active            == UVM_ACTIVE;
         obi_memory_instr_cfg.is_active == UVM_ACTIVE;
         obi_memory_data_cfg.is_active  == UVM_ACTIVE;
         rvfi_cfg.is_active             == UVM_PASSIVE;
         rvvi_cfg.is_active             == UVM_ACTIVE;
         fencei_cfg.is_active           == UVM_ACTIVE;
      }

      if (trn_log_enabled) {
         // Setting a reasonable set of logs
         clknrst_cfg.trn_log_enabled           == 0;
         debug_cfg.trn_log_enabled             == 0;
         interrupt_cfg.trn_log_enabled         == 0;
         isacov_cfg.trn_log_enabled            == 0;
         obi_memory_data_cfg.trn_log_enabled   == 1;
         obi_memory_instr_cfg.trn_log_enabled  == 1;
         rvfi_cfg.trn_log_enabled              == 1;
         rvvi_cfg.trn_log_enabled              == 1;
      } else {
         clknrst_cfg.trn_log_enabled           == 0;
         debug_cfg.trn_log_enabled             == 0;
         interrupt_cfg.trn_log_enabled         == 0;
         isacov_cfg.trn_log_enabled            == 0;
         obi_memory_data_cfg.trn_log_enabled   == 0;
         obi_memory_instr_cfg.trn_log_enabled  == 0;
         rvfi_cfg.trn_log_enabled              == 0;
         rvvi_cfg.trn_log_enabled              == 0;
      }

      if (cov_model_enabled) {
         isacov_cfg.cov_model_enabled            == 1;
         debug_cfg.cov_model_enabled             == 1;
         pma_cfg.cov_model_enabled               == 1;
         obi_memory_instr_cfg.cov_model_enabled  == 1;
         obi_memory_data_cfg.cov_model_enabled   == 1;
      }

      if (!scoreboarding_enabled) {
         buserr_scoreboarding_enabled == 0;
         pma_cfg.scoreboard_enabled   == 0;
      }
   }

   constraint obi_memory_instr_fault_cons {
      if (!obi_memory_instr_random_err_enabled) {
         obi_memory_instr_cfg.drv_slv_err_mode == UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_OK;
      } else {
         obi_memory_instr_cfg.drv_slv_err_mode == UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_RANDOM;
         obi_memory_instr_cfg.drv_slv_err_ok_wgt inside {[10:200]};
         obi_memory_instr_cfg.drv_slv_err_fault_wgt == 1;
      }

      obi_memory_instr_cfg.drv_slv_err_one_shot_mode == obi_memory_instr_one_shot_err_enabled;
   }

   constraint obi_memory_data_fault_cons {
      if (!obi_memory_data_random_err_enabled) {
         obi_memory_data_cfg.drv_slv_err_mode == UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_OK;
      } else {
         obi_memory_data_cfg.drv_slv_err_mode == UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_RANDOM;
         obi_memory_data_cfg.drv_slv_err_ok_wgt inside {[10:200]};
         obi_memory_data_cfg.drv_slv_err_fault_wgt == 1;
      }

      obi_memory_data_cfg.drv_slv_err_one_shot_mode == obi_memory_data_one_shot_err_enabled;
   }

   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvme_cv32e40s_cfg");

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

   /**
    * Temporary override to remove User-mode CSRs that are not implemented yet
    */
   extern virtual function void set_unsupported_csr_mask();

endclass : uvme_cv32e40s_cfg_c

function uvme_cv32e40s_cfg_c::new(string name="uvme_cv32e40s_cfg");

   super.new(name);

   core_name = "CV32E40S";

   if ($test$plusargs("USE_ISS"))
      use_iss = 1;
   if ($test$plusargs("trn_log_disabled")) begin
      trn_log_enabled = 0;
      trn_log_enabled.rand_mode(0);
   end
   if ($test$plusargs("buserr_sb_disabled")) begin
      buserr_scoreboarding_enabled = 0;
      buserr_scoreboarding_enabled.rand_mode(0);
   end

   if ($test$plusargs("obi_memory_instr_random_err"))
      obi_memory_instr_random_err_enabled = 1;
   if ($test$plusargs("obi_memory_instr_one_shot_err"))
      obi_memory_instr_one_shot_err_enabled = 1;
   if ($test$plusargs("obi_memory_data_random_err"))
      obi_memory_data_random_err_enabled = 1;
   if ($test$plusargs("obi_memory_data_one_shot_err"))
      obi_memory_data_one_shot_err_enabled = 1;

   isacov_cfg = uvma_isacov_cfg_c::type_id::create("isacov_cfg");
   clknrst_cfg  = uvma_clknrst_cfg_c::type_id::create("clknrst_cfg");
   interrupt_cfg = uvma_interrupt_cfg_c::type_id::create("interrupt_cfg");
   debug_cfg = uvma_debug_cfg_c    ::type_id::create("debug_cfg");
   obi_memory_instr_cfg = uvma_obi_memory_cfg_c::type_id::create("obi_memory_instr_cfg");
   obi_memory_data_cfg  = uvma_obi_memory_cfg_c::type_id::create("obi_memory_data_cfg" );
   rvfi_cfg = uvma_rvfi_cfg_c#(ILEN,XLEN)::type_id::create("rvfi_cfg");
   rvvi_cfg = uvma_rvvi_ovpsim_cfg_c#(ILEN,XLEN)::type_id::create("rvvi_cfg");
   fencei_cfg = uvma_fencei_cfg_c::type_id::create("fencei_cfg");
   pma_cfg = uvma_pma_cfg_c#(ILEN,XLEN)::type_id::create("pma_cfg");

   obi_memory_instr_cfg.mon_logger_name = "OBII";
   obi_memory_data_cfg.mon_logger_name  = "OBID";

   isacov_cfg.core_cfg = this;
   rvfi_cfg.core_cfg = this;
   rvvi_cfg.core_cfg = this;

endfunction : new

function void uvme_cv32e40s_cfg_c::pre_randomize();

   `uvm_info("CFG", $sformatf("Pre-randomize num_mhpmcounters = %0d", num_mhpmcounters), UVM_LOW);

endfunction : pre_randomize

function void uvme_cv32e40s_cfg_c::post_randomize();

   super.post_randomize();

   rvfi_cfg.instr_name[0] = "INSTR";

   // Set volatile locations for virtual peripherals
   rvvi_cfg.add_volatile_mem_addr_range(CV_VP_REGISTER_BASE, CV_VP_REGISTER_BASE + CV_VP_REGISTER_SIZE - 1);

   // Disable some CSR checks from all tests
   configure_disable_csr_checks();

endfunction : post_randomize

function void uvme_cv32e40s_cfg_c::sample_parameters(uvma_core_cntrl_cntxt_c cntxt);

   uvma_cv32e40s_core_cntrl_cntxt_c e40s_cntxt;

   if (!$cast(e40s_cntxt, cntxt)) begin
      `uvm_fatal("SAMPLECNTXT", "Could not cast cntxt to uvma_cv32e40s_core_cntrl_cntxt_c");
   end

   num_mhpmcounters = e40s_cntxt.core_cntrl_vif.num_mhpmcounters;
   pma_regions      = new[e40s_cntxt.core_cntrl_vif.pma_cfg.size()];
   b_ext            = e40s_cntxt.core_cntrl_vif.b_ext;

   foreach (pma_regions[i]) begin
      pma_regions[i] = uvma_core_cntrl_pma_region_c::type_id::create($sformatf("pma_region%0d", i));
      pma_regions[i].word_addr_low  = e40s_cntxt.core_cntrl_vif.pma_cfg[i].word_addr_low;
      pma_regions[i].word_addr_high = e40s_cntxt.core_cntrl_vif.pma_cfg[i].word_addr_high;
      pma_regions[i].main           = e40s_cntxt.core_cntrl_vif.pma_cfg[i].main;
      pma_regions[i].bufferable     = e40s_cntxt.core_cntrl_vif.pma_cfg[i].bufferable;
      pma_regions[i].cacheable      = e40s_cntxt.core_cntrl_vif.pma_cfg[i].cacheable;
   end

   // Copy to the pma_configuration
   pma_cfg.regions = new[pma_regions.size()];
   foreach (pma_cfg.regions[i])
      pma_cfg.regions[i] = pma_regions[i];

endfunction : sample_parameters

function bit uvme_cv32e40s_cfg_c::is_csr_check_disabled(string name);

   // Fatal error if passed a CSR check which is non-existent
   if (!csr_name2addr.exists(name)) begin
      `uvm_fatal("CV32E40SCFG", $sformatf("CSR [%s] does not exist", name));
   end

   return disable_csr_check_mask[csr_name2addr[name]];

endfunction : is_csr_check_disabled

function void uvme_cv32e40s_cfg_c::configure_disable_csr_checks();

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

function void uvme_cv32e40s_cfg_c::set_unsupported_csr_mask();

   // FIXME:STRICHMO:When user mode CSRs are implemented on the e40s then remove this hack

   super.set_unsupported_csr_mask();

   // Now re-invalidate the user mode CSRs since they are not implemented, yet
   unsupported_csr_mask[uvma_core_cntrl_pkg::USTATUS] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::UIE] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::UTVEC] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::USCRATCH] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::UEPC] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::UCAUSE] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::UTVAL] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::UIP] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::CYCLE] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::TIME] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::INSTRET] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::CYCLEH] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::TIMEH] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::INSTRETH] = 1;
   unsupported_csr_mask[uvma_core_cntrl_pkg::SCOUNTEREN] = 1;

   // TODO:ropeders re-evaluate this when 40s is more stable
   unsupported_csr_mask[uvma_core_cntrl_pkg::TCONTROL] = 1;

   for (int i = 0; i < MAX_NUM_HPMCOUNTERS; i++) begin
      unsupported_csr_mask[uvma_core_cntrl_pkg::HPMCOUNTER3+i] = 1;
      unsupported_csr_mask[uvma_core_cntrl_pkg::HPMCOUNTER3H+i] = 1;
   end

endfunction : set_unsupported_csr_mask

`endif // __UVME_CV32E40S_CFG_SV__


