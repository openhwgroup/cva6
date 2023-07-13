// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVMA_OBI_MEMORY_COV_MODEL_SV__
`define __UVMA_OBI_MEMORY_COV_MODEL_SV__

   /*
   * Covergroups
   * Decalred at package-level to enable mutliple instances per monitor class (e.g. read/write)
   */
covergroup cg_obi_delay(string name) with function sample(uvma_obi_memory_mon_trn_c trn);
   option.per_instance = 1;
   option.name         = name;

   req_to_gnt: coverpoint (trn.gnt_latency) {
      bins dly[] = { [0:3] };
   }
   rready_to_rvalid: coverpoint (trn.rvalid_latency) {
      bins dly[] = { [0:3] };
   }

   dly_cross: cross req_to_gnt, rready_to_rvalid;

endgroup : cg_obi_delay

covergroup cg_obi(string name,
                  bit write_enabled,
                  bit read_enabled,
                  bit is_1p2)
   with function sample(uvma_obi_memory_mon_trn_c trn);

   option.per_instance = 1;
   option.name         = name;

   we: coverpoint (trn.access_type) {
      ignore_bins IGN_WRITE = {UVMA_OBI_MEMORY_ACCESS_WRITE} with ((item >= 0) && (!write_enabled));
      ignore_bins IGN_READ  = {UVMA_OBI_MEMORY_ACCESS_READ}  with ((item >= 0) && (!read_enabled));
      bins WRITE = {UVMA_OBI_MEMORY_ACCESS_WRITE};
      bins READ = {UVMA_OBI_MEMORY_ACCESS_READ};
   }

   memtype: coverpoint (trn.memtype) {
      ignore_bins IGN_MEMTYPE = {[0:$]} with ((item >= 0) && (!is_1p2));
   }

   prot: coverpoint (trn.prot) {
      ignore_bins IGN_MEMTYPE = {[0:$]} with ((item >= 0) && (!is_1p2));
      ignore_bins IGN_RSVD_PRIV = {3'b100, 3'b101};
   }

   err: coverpoint (trn.err) {
      ignore_bins IGN_ERR = {[0:$]} with ((item >=0 ) && (!is_1p2));
   }

endgroup : cg_obi

/**
 * Component encapsulating Open Bus Interface functional coverage model.
 */
class uvma_obi_memory_cov_model_c extends uvm_component;
   
   // Objects
   uvma_obi_memory_cfg_c            cfg;
   uvma_obi_memory_cntxt_c          cntxt;
   
   // TLM
   uvm_tlm_analysis_fifo#(uvma_obi_memory_mon_trn_c      )  mon_trn_fifo      ;
   uvm_tlm_analysis_fifo#(uvma_obi_memory_mstr_seq_item_c)  mstr_seq_item_fifo;
   uvm_tlm_analysis_fifo#(uvma_obi_memory_slv_seq_item_c )  slv_seq_item_fifo ;

   // Covergroup instances   
   cg_obi       obi_cg;
   cg_obi_delay wr_delay_cg;
   cg_obi_delay rd_delay_cg;

   `uvm_component_utils_begin(uvma_obi_memory_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_cov_model", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_memory_cov_model_c::sample_cfg()
    */
   extern function void sample_cfg();
   
   /**
    * TODO Describe uvma_obi_memory_cov_model_c::sample_cntxt()
    */
   extern function void sample_cntxt();
   
   /**
    * Sample covergroups for monitored OBI transactions
    */
   extern function void sample_mon_trn(uvma_obi_memory_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_obi_memory_cov_model_c::sample_mstr_seq_item()
    */
   extern function void sample_mstr_seq_item();
   
   /**
    * TODO Describe uvma_obi_memory_cov_model_c::sample_slv_seq_item()
    */
   extern function void sample_slv_seq_item();
   
endclass : uvma_obi_memory_cov_model_c


function uvma_obi_memory_cov_model_c::new(string name="uvma_obi_memory_cov_model", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


// A significant chunk of the build_phase method is common between this
// coverage model and the sequencer (uvma_obi_memory_sqr).  This is
// appropriate so the duplicated code has a lint waiver.
//
//@DVT_LINTER_WAIVER_START "MT20210901_1" disable SVTB.33.1.0, SVTB.33.2.0
function void uvma_obi_memory_cov_model_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_memory_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_obi_memory_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   mon_trn_fifo       = new("mon_trn_fifo"      , this);
   mstr_seq_item_fifo = new("mstr_seq_item_fifo", this);
   slv_seq_item_fifo  = new("slv_seq_item_fifo" , this);
   
   if (cfg.enabled && cfg.cov_model_enabled) begin
      obi_cg = new("obi_cg", 
                   .read_enabled(cfg.read_enabled), 
                   .write_enabled(cfg.write_enabled),
                   .is_1p2(cfg.version >= UVMA_OBI_MEMORY_VERSION_1P2));
      if (cfg.read_enabled)  rd_delay_cg = new("rd_delay_cg");
      if (cfg.write_enabled) wr_delay_cg = new("wr_delay_cg");
   end

endfunction : build_phase
//@DVT_LINTER_WAIVER_END "MT20210901_1"

task uvma_obi_memory_cov_model_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   if (cfg.enabled && cfg.cov_model_enabled) begin      
      fork
         // Configuration
         forever begin
            cntxt.sample_cfg_e.wait_trigger();
            sample_cfg();
         end
         
         // Context
         forever begin
            cntxt.sample_cntxt_e.wait_trigger();
            sample_cntxt();
         end
         
         // Monitor transactions
         forever begin
            uvma_obi_memory_mon_trn_c mon_trn;

            mon_trn_fifo.get(mon_trn);
            sample_mon_trn(mon_trn);
         end
         
         // 'mstr' sequence items
         forever begin
            uvma_obi_memory_mstr_seq_item_c mstr_seq_item;

            mstr_seq_item_fifo.get(mstr_seq_item);
            sample_mstr_seq_item();
         end
         
         // 'slv' sequence items
         forever begin
            uvma_obi_memory_slv_seq_item_c slv_seq_item;

            slv_seq_item_fifo.get(slv_seq_item);
            sample_slv_seq_item();
         end
      join_none
   end
   
endtask : run_phase


function void uvma_obi_memory_cov_model_c::sample_cfg();
   
   // TODO Implement uvma_obi_memory_cov_model_c::sample_cfg();
   
endfunction : sample_cfg


function void uvma_obi_memory_cov_model_c::sample_cntxt();
   
   // TODO Implement uvma_obi_memory_cov_model_c::sample_cntxt();
   
endfunction : sample_cntxt


function void uvma_obi_memory_cov_model_c::sample_mon_trn(uvma_obi_memory_mon_trn_c trn);
   
   obi_cg.sample(trn);
   if (cfg.write_enabled) wr_delay_cg.sample(trn);   
   if (cfg.read_enabled)  rd_delay_cg.sample(trn);   
   
endfunction : sample_mon_trn


function void uvma_obi_memory_cov_model_c::sample_mstr_seq_item();
   
   // TODO Implement uvma_obi_memory_cov_model_c::sample_mstr_seq_item();
   
endfunction : sample_mstr_seq_item


function void uvma_obi_memory_cov_model_c::sample_slv_seq_item();
   
   // TODO Implement uvma_obi_memory_cov_model_c::sample_slv_seq_item();
   
endfunction : sample_slv_seq_item


`endif // __UVMA_OBI_MEMORY_COV_MODEL_SV__

