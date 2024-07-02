// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
// Copyright 2021 Thales DIS Design Services SAS
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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_CVA6_CFG_SV__
`define __UVME_CVA6_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * CVA6 environment (uvme_cva6_env_c) components.
 */
class uvme_cva6_cfg_c extends uvma_core_cntrl_cfg_c;

   // Integrals
   rand bit                      enabled;

   rand bit                      scoreboard_enabled;
   rand bit                      tandem_enabled;
   rand bit                      cov_model_enabled;
   rand bit                      cov_cvxif_model_enabled;
   rand bit                      cov_isa_model_enabled;
   rand bit                      trn_log_enabled;
   rand int unsigned             sys_clk_period;

   // Agent cfg handles
   rand uvma_clknrst_cfg_c    clknrst_cfg;
   rand uvma_cvxif_cfg_c      cvxif_cfg;
   rand uvma_axi_cfg_c        axi_cfg;
   rand uvma_rvfi_cfg_c#(ILEN,XLEN)       rvfi_cfg;
   rand uvma_isacov_cfg_c                 isacov_cfg;

   // Zicond extension
   rand bit                      ext_zicond_supported;

   // HPDcache support
   rand bit                      HPDCache_supported;

   // pmp entries
   rand int                      nr_pmp_entries;

   // Zihpm extension
   rand bit                      ext_zihpm_supported;

   // Handle to RTL configuration
   rand cva6_cfg_t         CVA6Cfg;

   `uvm_object_utils_begin(uvme_cva6_cfg_c)
      `uvm_field_int (                         enabled                     , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active                   , UVM_DEFAULT          )
      `uvm_field_int (                         scoreboard_enabled          , UVM_DEFAULT          )
      `uvm_field_int (                         tandem_enabled              , UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled           , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled             , UVM_DEFAULT          )
      `uvm_field_int (                         ext_zicond_supported        , UVM_DEFAULT          )
      `uvm_field_int (                         HPDCache_supported          , UVM_DEFAULT          )
      `uvm_field_int (                         nr_pmp_entries              , UVM_DEFAULT          )
      `uvm_field_int (                         ext_zihpm_supported         , UVM_DEFAULT          )
      `uvm_field_int (                         sys_clk_period            , UVM_DEFAULT + UVM_DEC)

      `uvm_field_object(clknrst_cfg, UVM_DEFAULT)

      `uvm_field_object(cvxif_cfg, UVM_DEFAULT)

      `uvm_field_object(axi_cfg, UVM_DEFAULT)

      `uvm_field_object(rvfi_cfg,    UVM_DEFAULT)

      `uvm_field_object(isacov_cfg,  UVM_DEFAULT)

   `uvm_object_utils_end


   constraint defaults_cons {
      soft enabled                 == 1;
      soft is_active               == UVM_ACTIVE;
      soft scoreboard_enabled      == 1;
      soft cov_model_enabled       == 1;
      soft trn_log_enabled         == 1;
      soft sys_clk_period          == uvme_cva6_sys_default_clk_period; // see uvme_cva6_constants.sv
   }

   constraint cvxif_feature { //CV32A65X do not support dual read & write also the memory interface
      cvxif_cfg.dual_read_write_support_x  == 0;
      cvxif_cfg.load_store_support_x       == 0;
      cvxif_cfg.seq_cus_instr_x2_enabled   == 1;
      cvxif_cfg.reg_cus_crosses_enabled    == 0;
      cvxif_cfg.mode_s_supported           == CVA6Cfg.RVS;
      cvxif_cfg.mode_u_supported           == CVA6Cfg.RVU;
   }

   constraint cva6_riscv_cons {
      xlen == CVA6Cfg.XLEN;
      ilen == 32;

      ext_i_supported        == 1;
      ext_a_supported        == CVA6Cfg.RVA;
      ext_m_supported        == 1;
      ext_c_supported        == CVA6Cfg.RVC;
      ext_p_supported        == 0;
      ext_v_supported        == CVA6Cfg.RVV;
      ext_f_supported        == CVA6Cfg.RVF;
      ext_d_supported        == CVA6Cfg.RVD;
      ext_zba_supported      == CVA6Cfg.RVB;
      ext_zbb_supported      == CVA6Cfg.RVB;
      ext_zbc_supported      == CVA6Cfg.RVB;
      ext_zbe_supported      == 0;
      ext_zbf_supported      == 0;
      ext_zbm_supported      == 0;
      ext_zbp_supported      == 0;
      ext_zbr_supported      == 0;
      ext_zbs_supported      == CVA6Cfg.RVB;
      ext_zbt_supported      == 0;
      ext_zifencei_supported == 1;
      ext_zicsr_supported    == 1;
      ext_zicond_supported   == CVA6Cfg.RVZiCond;
      ext_zcb_supported      == CVA6Cfg.RVZCB;
      ext_zihpm_supported    == 0;
      ext_zicntr_supported   == 0;

      mode_s_supported       == CVA6Cfg.RVS;
      mode_u_supported       == CVA6Cfg.RVU;
      mode_h_supported       == CVA6Cfg.RVH;

      pmp_supported          == (CVA6Cfg.NrPMPEntries > 0);
      nr_pmp_entries         == 16;
      debug_supported        == CVA6Cfg.DebugEn;

      unaligned_access_supported     == 0;
      unaligned_access_amo_supported == 0;

      bitmanip_version        == BITMANIP_VERSION_1P00;
      priv_spec_version       == PRIV_VERSION_MASTER;
      endianness              == ENDIAN_LITTLE;

      boot_addr_valid         == 1;
      mtvec_addr_valid        == 1;
      dm_halt_addr_valid      == 1;
      dm_exception_addr_valid == 1;
      nmi_addr_valid          == 1;
      HPDCache_supported      == (CVA6Cfg.DCacheType == 2);

      DirectVecOnly           == CVA6Cfg.DirectVecOnly;
      TvalEn                  == CVA6Cfg.TvalEn;
   }

   constraint ext_const {
      if (!ext_c_supported) {
         ext_zcb_supported == 0;
      }
   }

   constraint pmp_const {
      if (!pmp_supported) {
         nr_pmp_entries == 0;
      }
      else {
         nr_pmp_entries inside {0, 16, 64};
      }
   }

   constraint default_cva6_boot_cons {
      (!mhartid_plusarg_valid)           -> (mhartid           == 'h0000_0000);
      (!mimpid_plusarg_valid)            -> (mimpid            == 'h0000_0000);
      (!boot_addr_plusarg_valid)         -> (boot_addr         == 'h8000_0000);
      (!mtvec_addr_plusarg_valid)        -> (mtvec_addr        == 'h0000_0000);
      (!nmi_addr_plusarg_valid)          -> (nmi_addr          == 'h0000_0000);
      (!dm_halt_addr_plusarg_valid)      -> (dm_halt_addr      == 'h0000_0000);
      (!dm_exception_addr_plusarg_valid) -> (dm_exception_addr == 'h0000_0000);
   }

   constraint agent_cfg_cons {
      if (enabled) {
         clknrst_cfg.enabled   == 1;
         isacov_cfg.enabled    == 1;
         rvfi_cfg.enabled      == 1;
      }

      isacov_cfg.seq_instr_group_x2_enabled == 1;
      isacov_cfg.seq_instr_group_x3_enabled == 0;
      isacov_cfg.seq_instr_group_x4_enabled == 0;
      isacov_cfg.seq_instr_x2_enabled       == 1;
      isacov_cfg.reg_crosses_enabled        == 0;
      isacov_cfg.reg_hazards_enabled        == 1;
      rvfi_cfg.nret                         == CVA6Cfg.NrCommitPorts;
      unified_traps                         == 0;
      axi_cfg.rand_channel_delay_enabled    == 0;

      if (is_active == UVM_ACTIVE) {
         clknrst_cfg.is_active   == UVM_ACTIVE;
         isacov_cfg.is_active    == UVM_PASSIVE;
         rvfi_cfg.is_active      == UVM_PASSIVE;
      }

      if (trn_log_enabled) {
         clknrst_cfg.trn_log_enabled   == 0;
         axi_cfg.trn_log_enabled       == 1;
         rvfi_cfg.trn_log_enabled      == 1;
         isacov_cfg.trn_log_enabled    == 1;
      }

      if (cov_model_enabled) {
         cvxif_cfg.cov_model_enabled  == 1;
         isacov_cfg.cov_model_enabled == 1;
         axi_cfg.cov_model_enabled == 1;
         //env coverage models
         cov_cvxif_model_enabled == 1;
         cov_isa_model_enabled   == 1;
      }

   }

   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvme_cva6_cfg");

      /**
    * Sample the parameters of the DUT via the virtual interface in a context
    */
   extern virtual function void sample_parameters(uvma_core_cntrl_cntxt_c cntxt);

   /**
    * Set unsupported_csr_mask based on extensions/modes supported
    */
   extern virtual function void set_unsupported_csr_mask();

endclass : uvme_cva6_cfg_c


function uvme_cva6_cfg_c::new(string name="uvme_cva6_cfg");

   super.new(name);

   clknrst_cfg  = uvma_clknrst_cfg_c::type_id::create("clknrst_cfg");
   cvxif_cfg    = uvma_cvxif_cfg_c::type_id::create("cvxif_cfg");
   axi_cfg      = uvma_axi_cfg_c::type_id::create("axi_cfg");
   rvfi_cfg     = uvma_rvfi_cfg_c#(ILEN,XLEN)::type_id::create("rvfi_cfg");
   isacov_cfg   = uvma_isacov_cfg_c::type_id::create("isacov_cfg");

   isacov_cfg.core_cfg = this;
   rvfi_cfg.core_cfg = this;

   $value$plusargs("core_name=%s", this.core_name);

endfunction : new

function void uvme_cva6_cfg_c::sample_parameters(uvma_core_cntrl_cntxt_c cntxt);

   uvma_cva6_core_cntrl_cntxt_c cva6_cntxt;

   if (!$cast(cva6_cntxt, cntxt)) begin
      `uvm_fatal("SAMPLECNTXT", "Could not cast cntxt to uvma_cva6_core_cntrl_cntxt_c");
   end


   num_mhpmcounters = cva6_cntxt.core_cntrl_vif.num_mhpmcounters;
   // TODO : Check PMA
   //~ pma_regions      = new[cva6_cntxt.core_cntrl_vif.pma_cfg.size()];

   //~ foreach (pma_regions[i]) begin
      //~ pma_regions[i] = uvma_core_cntrl_pma_region_c::type_id::create($sformatf("pma_region%0d", i));
      //~ pma_regions[i].word_addr_low  = cva6_cntxt.core_cntrl_vif.pma_cfg[i].word_addr_low;
      //~ pma_regions[i].word_addr_high = cva6_cntxt.core_cntrl_vif.pma_cfg[i].word_addr_high;
      //~ pma_regions[i].main           = cva6_cntxt.core_cntrl_vif.pma_cfg[i].main;
      //~ pma_regions[i].bufferable     = core_cntrl_vif.pma_cfg[i].bufferable;
      //~ pma_regions[i].cacheable      = core_cntrl_vif.pma_cfg[i].cacheable;
      //~ pma_regions[i].atomic         = core_cntrl_vif.pma_cfg[i].atomic;
   //~ end

   //~ // Copy to the pma_configuration
   //~ pma_cfg.regions = new[pma_regions.size()];
   //~ foreach (pma_cfg.regions[i])
      //~ pma_cfg.regions[i] = pma_regions[i];

endfunction : sample_parameters

function void uvme_cva6_cfg_c::set_unsupported_csr_mask();

   super.set_unsupported_csr_mask();

   // Remove unsupported CSRs for Embedded configuration
   unsupported_csr_mask[uvma_core_cntrl_pkg::MCOUNTINHIBIT] = 1;

   // Add supported CSRs for Embedded configuration
   for (int i = 0; i < MAX_NUM_HPMCOUNTERS; i++) begin
      unsupported_csr_mask[uvma_core_cntrl_pkg::MHPMEVENT3+i] = 0;
      if (xlen == 32) begin
         unsupported_csr_mask[uvma_core_cntrl_pkg::MHPMCOUNTER3+i] = 0;
         unsupported_csr_mask[uvma_core_cntrl_pkg::MHPMCOUNTER3H+i] = 0;
      end
      else if (xlen == 64) begin
         unsupported_csr_mask[uvma_core_cntrl_pkg::MHPMCOUNTER3+i] = 1;
         unsupported_csr_mask[uvma_core_cntrl_pkg::MHPMCOUNTER3H+i] = 1;
      end
   end

   // Zihpm extension CSRs
   if (ext_zihpm_supported) begin
      for (int i = 0; i < MAX_NUM_HPMCOUNTERS; i++) begin
         unsupported_csr_mask[uvma_core_cntrl_pkg::HPMCOUNTER3+i] = 0;
         if (xlen == 32) begin
            unsupported_csr_mask[uvma_core_cntrl_pkg::HPMCOUNTER3H+i] = 0;
         end
         else if (xlen ==64) begin
            unsupported_csr_mask[uvma_core_cntrl_pkg::HPMCOUNTER3H+i] = 1;
         end
      end
   end
   else begin
      for (int i = 0; i < MAX_NUM_HPMCOUNTERS; i++) begin
         unsupported_csr_mask[uvma_core_cntrl_pkg::HPMCOUNTER3+i] = 1;
         unsupported_csr_mask[uvma_core_cntrl_pkg::HPMCOUNTER3H+i] = 1;
      end
   end

   // Upper Machine mode CSRs
   if (xlen == 32) begin
      unsupported_csr_mask[uvma_core_cntrl_pkg::MSTATUSH] = 0;
      unsupported_csr_mask[uvma_core_cntrl_pkg::MCYCLEH] = 0;
      unsupported_csr_mask[uvma_core_cntrl_pkg::MINSTRETH] = 0;
   end
   else if (xlen == 64) begin
      unsupported_csr_mask[uvma_core_cntrl_pkg::MSTATUSH] = 1;
      unsupported_csr_mask[uvma_core_cntrl_pkg::MCYCLEH] = 1;
      unsupported_csr_mask[uvma_core_cntrl_pkg::MINSTRETH] = 1;
   end

   // Remove unsupported pmp CSRs
   if (nr_pmp_entries == 0) begin
       unsupported_csr_mask[uvma_core_cntrl_pkg::PMPCFG0+:16]  = 16'hffff;
       unsupported_csr_mask[uvma_core_cntrl_pkg::PMPADDR0+:64] = 64'hffffffffffffffff;
   end
   else if (nr_pmp_entries == 16) begin
       unsupported_csr_mask[uvma_core_cntrl_pkg::PMPCFG4+:12]   = 12'hfff;
       unsupported_csr_mask[uvma_core_cntrl_pkg::PMPADDR16+:48] = 48'hffffffffffff;
   end
   else if (nr_pmp_entries == 64) begin //if pmp entries is 64 we support all the pmp CSRs
       unsupported_csr_mask[uvma_core_cntrl_pkg::PMPCFG0+:16]  = 16'h0;
       unsupported_csr_mask[uvma_core_cntrl_pkg::PMPADDR0+:64] = 64'h0;
   end

endfunction : set_unsupported_csr_mask

`endif // __UVME_CVA6_CFG_SV__
