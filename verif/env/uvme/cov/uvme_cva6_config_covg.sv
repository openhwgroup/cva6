//
// Copyright 2020 OpenHW Group
// Copyright 2023 Thales DIS
//
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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

covergroup cg_cva6_config(string name) with function sample();

   option.per_instance = 1;
   option.name = name;

   cp_Xlen : coverpoint cva6_config_pkg::CVA6ConfigXlen {
      bins Xlen ={32};
   }
   cp_FpuEn : coverpoint cva6_config_pkg::CVA6ConfigFpuEn {
      bins FpuEn ={0};
   }
   cp_F16En : coverpoint cva6_config_pkg::CVA6ConfigF16En {
      bins F16En ={0};
   }
   cp_F16AltEn : coverpoint cva6_config_pkg::CVA6ConfigF16AltEn {
      bins F16AltEn ={0};
   }
   cp_F8En : coverpoint cva6_config_pkg::CVA6ConfigF8En {
      bins F8En ={0};
   }
   cp_FVecEn : coverpoint cva6_config_pkg::CVA6ConfigFVecEn {
      bins FVecEn ={0};
   }
   cp_CvxifEn : coverpoint cva6_config_pkg::CVA6ConfigCvxifEn {
      bins CvxifEn ={1};
   }
   cp_CExtEn : coverpoint cva6_config_pkg::CVA6ConfigCExtEn {
      bins CExtEn ={1};
   }
   cp_AExtEn : coverpoint cva6_config_pkg::CVA6ConfigAExtEn {
      bins AExtEn ={0};
   }
   cp_BExtEn : coverpoint cva6_config_pkg::CVA6ConfigBExtEn {
      bins BExtEn ={1};
   }
   cp_VExtEn : coverpoint cva6_config_pkg::CVA6ConfigVExtEn {
      bins VExtEn ={0};
   }
   cp_ZiCondExtEn : coverpoint cva6_config_pkg::CVA6ConfigZiCondExtEn {
      bins ZiCondExtEn ={0};
   }
   cp_AxiIdWidth : coverpoint cva6_config_pkg::CVA6ConfigAxiIdWidth {
      bins AxiIdWidth ={4};
   }
   cp_AxiAddrWidth : coverpoint cva6_config_pkg::CVA6ConfigAxiAddrWidth {
      bins AxiAddrWidth ={64};
   }
   cp_AxiDataWidth : coverpoint cva6_config_pkg::CVA6ConfigAxiDataWidth {
      bins AxiDataWidth ={64};
   }
   cp_FetchUserEn : coverpoint cva6_config_pkg::CVA6ConfigFetchUserEn {
      bins FetchUserEn ={0};
   }
   cp_FetchUserWidth : coverpoint cva6_config_pkg::CVA6ConfigFetchUserWidth {
      bins FetchUserWidth ={32};
   }
   cp_DataUserEn : coverpoint cva6_config_pkg::CVA6ConfigDataUserEn {
      bins DataUserEn ={0};
   }
   cp_DataUserWidth : coverpoint cva6_config_pkg::CVA6ConfigDataUserWidth {
      bins DataUserWidth ={32};
   }
   cp_IcacheByteSize : coverpoint cva6_config_pkg::CVA6ConfigIcacheByteSize {
      bins IcacheByteSize ={16384};
   }
   cp_IcacheSetAssoc : coverpoint cva6_config_pkg::CVA6ConfigIcacheSetAssoc {
      bins IcacheSetAssoc ={4};
   }
   cp_IcacheLineWidth : coverpoint cva6_config_pkg::CVA6ConfigIcacheLineWidth {
      bins IcacheLineWidth ={128};
   }
   cp_DcacheByteSize : coverpoint cva6_config_pkg::CVA6ConfigDcacheByteSize {
      bins DcacheByteSize ={32768};
   }
   cp_DcacheSetAssoc : coverpoint cva6_config_pkg::CVA6ConfigDcacheSetAssoc {
      bins DcacheSetAssoc ={8};
   }
   cp_DcacheLineWidth : coverpoint cva6_config_pkg::CVA6ConfigDcacheLineWidth {
      bins DcacheLineWidth ={128};
   }
   cp_DcacheIdWidth : coverpoint cva6_config_pkg::CVA6ConfigDcacheIdWidth {
      bins DcacheIdWidth ={1};
   }
   cp_MemTidWidth : coverpoint cva6_config_pkg::CVA6ConfigMemTidWidth {
      bins MemTidWidth ={2};
   }
   cp_WtDcacheWbufDepth : coverpoint cva6_config_pkg::CVA6ConfigWtDcacheWbufDepth {
      bins WtDcacheWbufDepth ={2};
   }
   cp_NrCommitPorts : coverpoint cva6_config_pkg::CVA6ConfigNrCommitPorts {
      bins NrCommitPorts ={1};
   }
   cp_NrScoreboardEntries : coverpoint cva6_config_pkg::CVA6ConfigNrScoreboardEntries {
      bins NrScoreboardEntries ={4};
   }
   cp_FPGAEn : coverpoint cva6_config_pkg::CVA6ConfigFPGAEn {
      bins FPGAEn ={0};
   }
   cp_NrLoadPipeRegs : coverpoint cva6_config_pkg::CVA6ConfigNrLoadPipeRegs {
      bins NrLoadPipeRegs ={0};
   }
   cp_NrStorePipeRegs : coverpoint cva6_config_pkg::CVA6ConfigNrStorePipeRegs {
      bins NrStorePipeRegs ={0};
   }
   cp_NrLoadBufEntries : coverpoint cva6_config_pkg::CVA6ConfigNrLoadBufEntries {
      bins NrLoadBufEntries ={2};
   }
   cp_InstrTlbEntries : coverpoint cva6_config_pkg::CVA6ConfigInstrTlbEntries {
      bins InstrTlbEntries ={2};
   }
   cp_DataTlbEntries : coverpoint cva6_config_pkg::CVA6ConfigDataTlbEntries {
      bins DataTlbEntries ={2};
   }
   cp_RASDepth : coverpoint cva6_config_pkg::CVA6ConfigRASDepth {
      bins RASDepth ={0};
   }
   cp_BTBEntries : coverpoint cva6_config_pkg::CVA6ConfigBTBEntries {
      bins BTBEntries ={0};
   }
   cp_BHTEntries : coverpoint cva6_config_pkg::CVA6ConfigBHTEntries {
      bins BHTEntries ={16};
   }
   cp_NrPMPEntries : coverpoint cva6_config_pkg::CVA6ConfigNrPMPEntries {
      bins NrPMPEntries ={8};
   }
   cp_PerfCounterEn : coverpoint cva6_config_pkg::CVA6ConfigPerfCounterEn {
      bins PerfCounterEn ={0};
   }
   cp_DcacheType : coverpoint cva6_config_pkg::CVA6ConfigDcacheType {
      bins DcacheType ={config_pkg::WT};
   }
   cp_MmuPresent : coverpoint cva6_config_pkg::CVA6ConfigMmuPresent {
      bins MmuPresent ={0};
   }
   cp_RvfiTrace : coverpoint cva6_config_pkg::CVA6ConfigRvfiTrace {
      bins RvfiTrace ={1};
   }
   // Extended
   cp_RVF : coverpoint cva6_config_pkg::cva6_cfg.RVF {
      bins RVF ={0};
   }
   cp_RVD : coverpoint cva6_config_pkg::cva6_cfg.RVD {
      bins RVD ={0};
   }
   cp_FpPresent : coverpoint cva6_config_pkg::cva6_cfg.FpPresent {
      bins FpPresent ={0};
   }
   cp_NSX : coverpoint cva6_config_pkg::cva6_cfg.NSX {
      bins NSX ={0};
   }
   cp_FLen : coverpoint cva6_config_pkg::cva6_cfg.FLen {
      bins FLen ={0};
   }
   cp_RVFVec : coverpoint cva6_config_pkg::cva6_cfg.RVFVec {
      bins RVFVec ={0};
   }
   cp_XF16Vec : coverpoint cva6_config_pkg::cva6_cfg.XF16Vec {
      bins XF16Vec ={0};
   }
   cp_XF16ALTVec : coverpoint cva6_config_pkg::cva6_cfg.XF16ALTVec {
      bins XF16ALTVec ={0};
   }
   cp_XF8Vec : coverpoint cva6_config_pkg::cva6_cfg.XF8Vec {
      bins XF8Vec ={0};
   }
   cp_NrRgprPorts : coverpoint cva6_config_pkg::cva6_cfg.NrRgprPorts {
      bins NrRgprPorts ={0};
   }
   cp_NrWbPorts : coverpoint cva6_config_pkg::cva6_cfg.NrWbPorts {
      bins NrWbPorts ={0};
   }
   cp_EnableAccelerator : coverpoint cva6_config_pkg::cva6_cfg.EnableAccelerator {
      bins EnableAccelerator ={0};
   }
   cp_HaltAddress : coverpoint cva6_config_pkg::cva6_cfg.HaltAddress {
      bins HaltAddress ={64'h800};
   }
   cp_ExceptionAddress : coverpoint cva6_config_pkg::cva6_cfg.ExceptionAddress {
      bins ExceptionAddress ={64'h808};
   }
endgroup: cg_cva6_config

covergroup cg_cva6_boot_addr(string name) with function sample(bit [cva6_config_pkg::CVA6ConfigXlen-1:0] boot_addr);
   option.per_instance = 1;
   option.name = name;
   
   cp_boot_addr : coverpoint boot_addr {
      bins BOOT_ADDR_0 ={0};
      bins BOOT_ADDR_LOW ={[1:'h10000_0000]};
      bins BOOT_ADDR_HIGH ={['h10000_0000:$]};
   }
endgroup: cg_cva6_boot_addr

covergroup cg_cva6_clock_period_cg(string name) with function sample(int clock_period_ps);
   option.per_instance = 1;
   option.name = name;
   
   cp_clock_period_ps : coverpoint clock_period_ps {
      bins LOW   = {[0:1500]};
      bins HIGH  = {[1501:6670]};
   }
endgroup: cg_cva6_clock_period_cg

covergroup cg_cva6_reset_cg(string name,int clock_period_ps) with function sample(uvma_clknrst_mon_trn_c trn);
   option.per_instance = 1;
   option.name = name;
   
   cp_reset : coverpoint trn.event_type {
      bins ASSERTED   = {UVMA_CLKNRST_MON_TRN_EVENT_RESET_ASSERTED};
      bins DEASSERTED = {UVMA_CLKNRST_MON_TRN_EVENT_RESET_DEASSERTED};
   }

   cp_reset_duration_ps : coverpoint int'(trn.reset_pulse_length/1ps) iff(trn.event_type == UVMA_CLKNRST_MON_TRN_EVENT_RESET_DEASSERTED) {
      bins SHORT = {[0:clock_period_ps]};
      bins LONG  = {[clock_period_ps+1:$]};
   }

   cp_reset_onthefly_assert : coverpoint trn.event_type {
      bins onthefly_assert   = (UVMA_CLKNRST_MON_TRN_EVENT_RESET_DEASSERTED=>UVMA_CLKNRST_MON_TRN_EVENT_RESET_ASSERTED=>UVMA_CLKNRST_MON_TRN_EVENT_RESET_DEASSERTED);
   }

endgroup: cg_cva6_reset_cg

class uvme_cva6_config_covg_c extends uvm_component;

   // Objects
   uvme_cva6_cfg_c         cfg      ;
   uvme_cva6_cntxt_c       cntxt    ;
   
   `uvm_analysis_imp_decl(_reset)
   uvm_analysis_imp_reset #(uvma_clknrst_mon_trn_c, uvme_cva6_config_covg_c) reset_imp;
   
   `uvm_component_utils_begin(uvme_cva6_config_covg_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   // Covergroups
   cg_cva6_config          config_cg;
   cg_cva6_boot_addr       boot_addr_cg;
   cg_cva6_clock_period_cg clock_period_cg;
   cg_cva6_reset_cg        reset_cg;
   
   extern function new(string name = "uvme_cva6_config_covg_c", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern task run_phase(uvm_phase phase);
   extern function void sample_cva6_config();
   extern function void write_reset(uvma_clknrst_mon_trn_c trn);

endclass : uvme_cva6_config_covg_c

function uvme_cva6_config_covg_c::new(string name = "uvme_cva6_config_covg_c", uvm_component parent = null);

   super.new(name, parent);
   reset_imp = new("rest_imp", this);
endfunction : new

function void uvme_cva6_config_covg_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvme_cva6_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   config_cg       = new("config_cg");
   boot_addr_cg    = new("boot_addr_cg");
   clock_period_cg = new("clock_period_cg");
   reset_cg        = new("reset_cg",cfg.sys_clk_period);
   
endfunction : build_phase

function void uvme_cva6_config_covg_c::sample_cva6_config();

   config_cg.sample();
   boot_addr_cg.sample(cfg.boot_addr);
   clock_period_cg.sample(cfg.sys_clk_period);
   
endfunction : sample_cva6_config

function void uvme_cva6_config_covg_c::write_reset(uvma_clknrst_mon_trn_c trn);

   reset_cg.sample(trn); 

endfunction

task uvme_cva6_config_covg_c::run_phase(uvm_phase phase);

   super.run_phase(phase);
   
   sample_cva6_config();

endtask : run_phase
