// Copyright 2021 OpenHW Group
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVMA_PMA_COV_MODEL_SV__
`define __UVMA_PMA_COV_MODEL_SV__

covergroup cg_pma_default_access(
   string name
) with function sample(uvma_pma_mon_trn_c           trn);
   option.name = name;
   `per_instance_fcov

   cp_access: coverpoint(trn.access) {
      bins INSTR = {UVMA_PMA_ACCESS_INSTR};
      bins DATA  = {UVMA_PMA_ACCESS_DATA};
   }

   cp_rw: coverpoint(trn.rw) {
      bins READ  = {UVMA_PMA_RW_READ};
      bins WRITE = {UVMA_PMA_RW_WRITE};
   }

   cross_pma: cross cp_access, cp_rw {
      ignore_bins IGN_INSTR_WRITE = binsof(cp_rw) intersect {UVMA_PMA_RW_WRITE} &&
                                    binsof(cp_access) intersect {UVMA_PMA_ACCESS_INSTR};
   }

endgroup :  cg_pma_default_access

covergroup cg_pma_deconfigured_access(
   string name
) with function sample(uvma_pma_mon_trn_c           trn);
   option.name = name;
   `per_instance_fcov

   cp_access: coverpoint(trn.access) {
      bins INSTR = {UVMA_PMA_ACCESS_INSTR};
      bins DATA  = {UVMA_PMA_ACCESS_DATA};
   }

   cp_rw: coverpoint(trn.rw) {
      bins READ  = {UVMA_PMA_RW_READ};
      bins WRITE = {UVMA_PMA_RW_WRITE};
   }

   cross_pma: cross cp_access, cp_rw {
      ignore_bins IGN_INSTR_WRITE = binsof(cp_rw) intersect {UVMA_PMA_RW_WRITE} &&
                                    binsof(cp_access) intersect {UVMA_PMA_ACCESS_INSTR};
   }

endgroup :  cg_pma_deconfigured_access

/**
 * Component encapsulating PMA agent for OpenHW Group CORE-V verification testbenches functional coverage model.
 */
class uvma_pma_cov_model_c extends uvm_component;

   // Objects
   uvma_pma_cfg_c       cfg;
   uvma_pma_mon_trn_c   mon_trn;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_pma_mon_trn_c)  mon_trn_fifo;

   // Covergroups
   cg_pma_default_access      pma_default_access_covg;
   cg_pma_deconfigured_access pma_deconfigured_access_covg;

   `uvm_component_utils_begin(uvma_pma_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_pma_cov_model", uvm_component parent=null);

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
    * TODO Describe uvma_pma_cov_model_c::sample_mon_trn()
    */
   extern function void sample_mon_trn();

endclass : uvma_pma_cov_model_c


function uvma_pma_cov_model_c::new(string name="uvma_pma_cov_model", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_pma_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_pma_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   if (cfg.trn_log_enabled && cfg.cov_model_enabled) begin
      if (cfg.regions.size()) begin
         pma_default_access_covg = new("pma_default_access_covg");
      end
      else begin
         pma_deconfigured_access_covg = new("pma_deconfigured_access_covg");
      end
   end

   mon_trn_fifo  = new("mon_trn_fifo" , this);

endfunction : build_phase


task uvma_pma_cov_model_c::run_phase(uvm_phase phase);

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


function void uvma_pma_cov_model_c::sample_mon_trn();

   // This coverage model will only sample for deconfigured PMA or
   // a PMA access that does not map to a configured region
   if (mon_trn.is_default) begin
      if (cfg.regions.size() == 0) begin
         pma_deconfigured_access_covg.sample(mon_trn);
      end
      else begin
         pma_default_access_covg.sample(mon_trn);
      end
   end

endfunction : sample_mon_trn


`endif // __UVMA_PMA_COV_MODEL_SV__

