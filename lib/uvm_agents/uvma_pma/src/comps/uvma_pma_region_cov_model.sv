// Copyright 2021 OpenHW Group
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVMA_PMA_REGION_COV_MODEL_SV__
`define __UVMA_PMA_REGION_COV_MODEL_SV__

covergroup cg_pma_access(
   string name
) with function sample(uvma_pma_mon_trn_c           trn,
                       uvma_core_cntrl_pma_region_c pma_region);
   option.name = name;
   `per_instance_fcov

   cp_first_word: coverpoint (trn.is_first_word) {
      bins FIRST = {1};
   }

   cp_last_word: coverpoint (trn.is_last_word) {
      bins LAST = {1};
   }

   cp_main: coverpoint (pma_region.main) {
      bins IO   = {0};
      bins MAIN = {1};
   }

   cp_bufferable: coverpoint (pma_region.bufferable) {
      bins NONBUF = {0};
      bins BUF    = {1};
   }

   cp_cacheable: coverpoint (pma_region.cacheable) {
      bins NONCACHE = {0};
      bins CACHE    = {1};
   }

   cp_atomic: coverpoint (pma_region.atomic) {
      bins NONATOMIC = {0};
      bins ATOMIC    = {1};
   }

   cp_access: coverpoint(trn.access) {
      bins INSTR = {UVMA_PMA_ACCESS_INSTR};
      bins DATA  = {UVMA_PMA_ACCESS_DATA};
   }

   cp_rw: coverpoint(trn.rw) {
      bins READ  = {UVMA_PMA_RW_READ};
      bins WRITE = {UVMA_PMA_RW_WRITE};
   }

   cross_pma: cross cp_main, cp_bufferable, cp_cacheable, cp_atomic, cp_access, cp_rw {
      ignore_bins IGN_INSTR_WRITE = binsof(cp_rw) intersect {UVMA_PMA_RW_WRITE} &&
                                    binsof(cp_access) intersect {UVMA_PMA_ACCESS_INSTR};
      ignore_bins IGN_INSTR_IO = binsof(cp_main) intersect {0} &&
                                 binsof(cp_access) intersect {UVMA_PMA_ACCESS_INSTR};
   }

endgroup :  cg_pma_access

/**
 * Component encapsulating PMA coverage model for a single PMA region
 */
class uvma_pma_region_cov_model_c extends uvm_component;

   // Objects
   uvma_pma_cfg_c       cfg;
   uvma_pma_mon_trn_c   mon_trn;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_pma_mon_trn_c)  mon_trn_fifo;

   // Region index for this coverage model index
   int                  region_index;

   // Covergroups
   cg_pma_access        pma_access_covg;

   `uvm_component_utils_begin(uvma_pma_region_cov_model_c)
      `uvm_field_object(cfg       , UVM_DEFAULT)
      `uvm_field_int(region_index , UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_pma_region_cov_model", uvm_component parent=null);

   /**
    * 1. Ensures cfg handle is not null.
    * 2. Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * TODO Describe uvma_pma_region_cov_model_c::sample_mon_trn()
    */
   extern function void sample_mon_trn();

endclass : uvma_pma_region_cov_model_c


function uvma_pma_region_cov_model_c::new(string name="uvma_pma_region_cov_model", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_pma_region_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_pma_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   if (cfg.trn_log_enabled && cfg.cov_model_enabled) begin
      if (cfg.regions.size()) begin
         pma_access_covg = new("pma_access_covg");
      end
   end

   mon_trn_fifo  = new("mon_trn_fifo" , this);

endfunction : build_phase


task uvma_pma_region_cov_model_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   fork
      // Monitor transactions
      forever begin
         mon_trn_fifo.get(mon_trn);
         if (cfg.enabled && cfg.cov_model_enabled) begin
            sample_mon_trn();
         end
      end

   join_none

endtask : run_phase


function void uvma_pma_region_cov_model_c::sample_mon_trn();

   if (!mon_trn.is_default && mon_trn.region_index == this.region_index) begin
      pma_access_covg.sample(mon_trn, cfg.regions[mon_trn.region_index]);
   end

endfunction : sample_mon_trn


`endif // __UVMA_PMA_REGION_COV_MODEL_SV__

