// Copyright 2021 OpenHW Group
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVMA_PMA_SB_SV__
`define __UVMA_PMA_SB_SV__

/**
 * Component sampling transactions from a Memory attribution agent for OpenHW Group CORE-V verification testbenches virtual interface (uvma_pma_if).
 */
class uvma_pma_sb_c#(int ILEN=DEFAULT_ILEN,
                     int XLEN=DEFAULT_XLEN) extends uvm_component;

   // Objects
   uvma_pma_cfg_c    cfg;

   // Counters
   int unsigned obi_i_checked_cnt;
   int unsigned obi_d_checked_cnt;

   // TLM exports
   uvm_analysis_imp_rvfi_instr#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvma_pma_sb_c)  rvfi_instr_export;
   uvm_analysis_imp_obi_i#(uvma_obi_memory_mon_trn_c, uvma_pma_sb_c)                    obi_i_export;
   uvm_analysis_imp_obi_d#(uvma_obi_memory_mon_trn_c, uvma_pma_sb_c)                    obi_d_export;

   `uvm_component_param_utils_begin(uvma_pma_sb_c#(ILEN,XLEN))
      `uvm_field_object(cfg           , UVM_DEFAULT)
      `uvm_field_int(obi_i_checked_cnt, UVM_DEFAULT)
      `uvm_field_int(obi_d_checked_cnt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_pma_sb", uvm_component parent=null);

   /**
    * Ensures cfg handle is not null.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Oversees monitoring, depending on the reset state, by calling mon_<pre|in|post>_reset() tasks.
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Report stats from checker
    */
   extern virtual function void report_phase(uvm_phase phase);

   /**
    * Print out checked counters when aborting test due to fatal or too many errors
    */
   extern function void pre_abort();

   /**
    * RVFI instructions
    */
   extern virtual function void write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) instr);

   /**
    * OBI instruction
    */
   extern virtual function void write_obi_i(uvma_obi_memory_mon_trn_c obi);

   /**
    * OBI data
    */
   extern virtual function void write_obi_d(uvma_obi_memory_mon_trn_c obi);

   /**
    * Check an OBI instruction fetch for a deconfigured PMA region (PMA disabled)
    */
   extern virtual function void check_obi_i_deconfigured(uvma_obi_memory_mon_trn_c obi);

   /**
    * Check an OBI instruction fetch for a mappped region
    */
   extern virtual function void check_obi_i_mapped_region(uvma_obi_memory_mon_trn_c obi, int index);

   /**
    * Check an OBI instruction fetch for a default PMA region (PMA enabled, but address does not map to any region)
    */
   extern virtual function void check_obi_i_default_region(uvma_obi_memory_mon_trn_c obi);

   /**
    * Check an OBI data accessfor a deconfigured PMA region (PMA disabled)
    */
   extern virtual function void check_obi_d_deconfigured(uvma_obi_memory_mon_trn_c obi);

   /**
    * Check an OBI data access for a mappped region
    */
   extern virtual function void check_obi_d_mapped_region(uvma_obi_memory_mon_trn_c obi, int index);

   /**
    * Check an OBI data access for a default PMA region (PMA enabled, but address does not map to any region)
    */
   extern virtual function void check_obi_d_default_region(uvma_obi_memory_mon_trn_c obi);

   /**
    * Common print report state
    */
   extern virtual function void print_checked_stats();

endclass : uvma_pma_sb_c


function uvma_pma_sb_c::new(string name="uvma_pma_sb", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_pma_sb_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_pma_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   rvfi_instr_export = new("rvfi_instr_export", this);
   obi_i_export      = new("obi_i_export",      this);
   obi_d_export      = new("obi_d_export",      this);
endfunction : build_phase

task uvma_pma_sb_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

endtask : run_phase

function void uvma_pma_sb_c::write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) instr);

endfunction : write_rvfi_instr


function void uvma_pma_sb_c::write_obi_i(uvma_obi_memory_mon_trn_c obi);

   int index;

   // If scoreboard not enabled, then bail out
   if (!cfg.scoreboard_enabled)
      return;

   // Will check this OBI
   obi_i_checked_cnt++;

   // If deconfigured then check directly
   if (cfg.regions.size() == 0) begin
      check_obi_i_deconfigured(obi);

      return;
   end

   // Get expected index of the OBI transaction
   index = cfg.get_pma_region_for_addr(obi.address);

   // If the region does not map, then we are in the default OBI region
   if (index == -1) begin
      check_obi_i_default_region(obi);

      return;
   end

   check_obi_i_mapped_region(obi, index);

endfunction : write_obi_i

function void uvma_pma_sb_c::write_obi_d(uvma_obi_memory_mon_trn_c obi);

   int index;

   // If scoreboard not enabled, then bail out
   if (!cfg.scoreboard_enabled)
      return;

   obi_d_checked_cnt++;

   // If deconfigured then check directly
   if (cfg.regions.size() == 0) begin
      check_obi_d_deconfigured(obi);

      return;
   end

   // Get expected index of the OBI transaction
   index = cfg.get_pma_region_for_addr(obi.address);

   // If the region does not map, then we are in the default OBI region
   if (index == -1) begin
      check_obi_d_default_region(obi);

      return;
   end

   check_obi_d_mapped_region(obi, index);

endfunction : write_obi_d

function void uvma_pma_sb_c::report_phase(uvm_phase phase);

   print_checked_stats();

endfunction : report_phase

function void uvma_pma_sb_c::pre_abort();

   print_checked_stats();

endfunction : pre_abort

function void uvma_pma_sb_c::print_checked_stats();

   `uvm_info("PMASB", $sformatf("checked %0d OBI I transactions", obi_i_checked_cnt), UVM_NONE);
   `uvm_info("PMASB", $sformatf("checked %0d OBI D transactions", obi_d_checked_cnt), UVM_NONE);

endfunction : print_checked_stats

function void uvma_pma_sb_c::check_obi_i_deconfigured(uvma_obi_memory_mon_trn_c obi);

   // Check: Bufferable bit must be 0 in OBI for instruction fetches
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_BUFFERABLE_BIT]) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x bufferable bit set for deconfigured PMA",
                                       obi.access_type.name(), obi.address));
   end

   // Check: Cacheable bit must be 0 in OBI
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_CACHEABLE_BIT]) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x cacheable bit set for deconfigured PMA",
                                       obi.access_type.name(), obi.address));
   end

   // Check: atomic attributes should be 0
   if (obi.atop) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x atop is not zero, OBI: 0x%0x",
                                       obi.access_type.name(), obi.address,
                                       obi.atop));
   end

endfunction : check_obi_i_deconfigured

function void uvma_pma_sb_c::check_obi_i_default_region(uvma_obi_memory_mon_trn_c obi);

   // Check: Bufferable bit must be 0 in OBI for instruction fetches
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_BUFFERABLE_BIT]) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x bufferable bit set for PMA default region",
                                       obi.access_type.name(), obi.address));
   end

   // Check: Cacheable bit must be 0 in OBI
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_CACHEABLE_BIT]) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x cacheable bit set for PMA default region",
                                       obi.access_type.name(), obi.address));
   end

   // Check: atomic attributes should be 0
   if (obi.atop) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x atop is not zero, OBI: 0x%0x",
                                       obi.access_type.name(), obi.address,
                                       obi.atop));
   end

endfunction : check_obi_i_default_region

function void uvma_pma_sb_c::check_obi_i_mapped_region(uvma_obi_memory_mon_trn_c obi, int index);

   // Check: Must be main memory
   if (!cfg.regions[index].main) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x, region: %0d instruction fetch from I/O memory",
                                       obi.access_type.name(), obi.address, index));
   end

   // Check: Bufferable bit must be 0 in OBI for instruction fetches
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_BUFFERABLE_BIT]) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x bufferable bit set for PMA default region",
                                       obi.access_type.name(), obi.address));
   end

   // Check: Cacheable bit must match mem_type[0] in OBI
   if (obi.memtype[1] != cfg.regions[index].cacheable) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x, region: %0d cacheable bit mismatch, OBI: %0d, PMA: %0d",
                                       obi.access_type.name(), obi.address, index,
                                       obi.memtype[1], cfg.regions[index].cacheable));
   end

   // Check: atomic attributes should be 0
   if (obi.atop) begin
      `uvm_error("PMAOBII", $sformatf("OBI I %s address: 0x%08x, region: %0d atop is not zero, OBI: 0x%0x",
                                       obi.access_type.name(), obi.address, index,
                                       obi.atop));
   end

endfunction : check_obi_i_mapped_region

function void uvma_pma_sb_c::check_obi_d_deconfigured(uvma_obi_memory_mon_trn_c obi);

   // Check: Bufferable bit must be 0 in OBI
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_BUFFERABLE_BIT]) begin
      `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x bufferable bit set for deconfigured PMA",
                                       obi.access_type.name(), obi.address));
   end

   // Check: Cacheable bit must be 0 in OBI
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_CACHEABLE_BIT]) begin
      `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x cacheable bit set for deconfigured PMA",
                                       obi.access_type.name(), obi.address));
   end

endfunction : check_obi_d_deconfigured

function void uvma_pma_sb_c::check_obi_d_default_region(uvma_obi_memory_mon_trn_c obi);

   // Check: Bufferable bit must be 0 in OBI
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_BUFFERABLE_BIT]) begin
      `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x bufferable bit set for PMA default region",
                                       obi.access_type.name(), obi.address));
   end

   // Check: Cacheable bit must be 0 in OBI
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_CACHEABLE_BIT]) begin
      `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x cacheable bit set for PMA default region",
                                       obi.access_type.name(), obi.address));
   end

   // Check: atomic attributes should be 0
   if (obi.atop) begin
      `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x atop is not zero for PMA default region, OBI: 0x%0x",
                                       obi.access_type.name(), obi.address,
                                       obi.atop));
   end

endfunction : check_obi_d_default_region


function void uvma_pma_sb_c::check_obi_d_mapped_region(uvma_obi_memory_mon_trn_c obi, int index);


   if (obi.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      // Check: Bufferable bit must be 0 in OBI for data loads
      if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_BUFFERABLE_BIT]) begin
         `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x, region: %0d bufferable bit set for data load",
                                          obi.access_type.name(), obi.address, index));
      end
   end
   else begin
      // Check: Bufferable bit must match mem_type[0] in OBI
      if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_BUFFERABLE_BIT] != cfg.regions[index].bufferable) begin
         `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x, region: %0d bufferable bit mismatch, OBI: %0d, PMA: %0d",
                                          obi.access_type.name(), obi.address, index,
                                          obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_BUFFERABLE_BIT], cfg.regions[index].bufferable));
      end
   end

   // Check: Cacheable bit must match mem_type[0] in OBI
   if (obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_CACHEABLE_BIT] != cfg.regions[index].cacheable) begin
      `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x, region: %0d cacheable bit mismatch, OBI: %0d, PMA: %0d",
                                       obi.access_type.name(), obi.address, index,
                                       obi.memtype[UVMA_OBI_MEMORY_MEMTYPE_CACHEABLE_BIT], cfg.regions[index].cacheable));
   end

   // Check: atomic attributes should be 0
   if (obi.atop) begin
      `uvm_error("PMAOBID", $sformatf("OBI D %s address: 0x%08x, region: %0d atop is not zero, OBI: 0x%0x",
                                       obi.access_type.name(), obi.address, index,
                                       obi.atop));
   end

endfunction : check_obi_d_mapped_region

`endif // __UVMA_PMA_SB_SV__
