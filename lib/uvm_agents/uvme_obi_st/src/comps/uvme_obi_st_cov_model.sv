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


`ifndef __UVME_OBI_ST_COV_MODEL_SV__
`define __UVME_OBI_ST_COV_MODEL_SV__


/**
 * Component encapsulating AMBA Advanced eXtensible Interface Self-Test Environment functional
 * coverage model.
 */
class uvme_obi_st_cov_model_c extends uvm_component;
   
   // Coverage targets
   uvme_obi_st_cfg_c         cfg;
   uvme_obi_st_cntxt_c       cntxt;
   uvma_obi_memory_mstr_seq_item_c  mstr_seq_item;
   uvma_obi_memory_slv_seq_item_c   slv_seq_item;
   uvma_obi_memory_mon_trn_c        mstr_mon_trn;
   uvma_obi_memory_mon_trn_c        slv_mon_trn;
   
   // TLM
   uvm_tlm_analysis_fifo#(uvma_obi_memory_mstr_seq_item_c)  mstr_seq_item_fifo;
   uvm_tlm_analysis_fifo#(uvma_obi_memory_slv_seq_item_c )  slv_seq_item_fifo ;
   uvm_tlm_analysis_fifo#(uvma_obi_memory_mon_trn_c      )  mstr_mon_trn_fifo ;
   uvm_tlm_analysis_fifo#(uvma_obi_memory_mon_trn_c      )  slv_mon_trn_fifo  ;
   
   
   `uvm_component_utils_begin(uvme_obi_st_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   covergroup obi_st_cfg_cg;
      // TODO Implement obi_st_cfg_cg
      //      Ex: abc_cpt : coverpoint cfg.abc;
      //          xyz_cpt : coverpoint cfg.xyz;
   endgroup : obi_st_cfg_cg
   
   covergroup obi_st_cntxt_cg;
      // TODO Implement obi_st_cntxt_cg
      //      Ex: abc_cpt : coverpoint cntxt.abc;
      //          xyz_cpt : coverpoint cntxt.xyz;
   endgroup : obi_st_cntxt_cg
   
   covergroup obi_st_mstr_seq_item_cg;
      // TODO Implement obi_st_mstr_seq_item_cg
      //      Ex: abc_cpt : coverpoint mstr_seq_item.abc;
      //          xyz_cpt : coverpoint mstr_seq_item.xyz;
   endgroup : obi_st_mstr_seq_item_cg
   
   covergroup obi_st_slv_seq_item_cg;
      // TODO Implement obi_st_slv_seq_item_cg
      //      Ex: abc_cpt : coverpoint slv_seq_item.abc;
      //          xyz_cpt : coverpoint slv_seq_item.xyz;
   endgroup : obi_st_slv_seq_item_cg
   
   covergroup obi_st_mstr_mon_trn_cg;
      // TODO Implement obi_st_mstr_mon_trn_cg
      //      Ex: abc_cpt : coverpoint mon_trn.abc;
      //          xyz_cpt : coverpoint mon_trn.xyz;
   endgroup : obi_st_mstr_mon_trn_cg
   
   covergroup obi_st_slv_mon_trn_cg;
      // TODO Implement obi_st_slv_mon_trn_cg
      //      Ex: abc_cpt : coverpoint mon_trn.abc;
      //          xyz_cpt : coverpoint mon_trn.xyz;
   endgroup : obi_st_slv_mon_trn_cg
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_obi_st_cov_model", uvm_component parent=null);
   
   /**
    * Ensures cfg & cntxt handles are not null.
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * Describe uvme_obi_st_cov_model_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvme_obi_st_cov_model_c::sample_cfg()
    */
   extern function void sample_cfg();
   
   /**
    * TODO Describe uvme_obi_st_cov_model_c::sample_cntxt()
    */
   extern function void sample_cntxt();
   
   /**
    * TODO Describe uvme_obi_st_cov_model_c::sample_mstr_seq_item()
    */
   extern function void sample_mstr_seq_item();
   
   /**
    * TODO Describe uvme_obi_st_cov_model_c::sample_slv_seq_item()
    */
   extern function void sample_slv_seq_item();
   
   /**
    * TODO Describe uvme_obi_st_cov_model_c::sample_mstr_mon_trn()
    */
   extern function void sample_mstr_mon_trn();
   
   /**
    * TODO Describe uvme_obi_st_cov_model_c::sample_slv_mon_trn()
    */
   extern function void sample_slv_mon_trn();
   
endclass : uvme_obi_st_cov_model_c


function uvme_obi_st_cov_model_c::new(string name="uvme_obi_st_cov_model", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvme_obi_st_cov_model_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvme_obi_st_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvme_obi_st_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   // Build TLM objects
   mstr_seq_item_fifo = new("mstr_seq_item_fifo", this);
   slv_seq_item_fifo  = new("slv_seq_item_fifo" , this);
   mstr_mon_trn_fifo  = new("mstr_mon_trn_fifo" , this);
   slv_mon_trn_fifo   = new("slv_mon_trn_fifo"  , this);
   
endfunction : build_phase


task uvme_obi_st_cov_model_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
  
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
    
    // 'mstr' sequence item coverage
    forever begin
       mstr_seq_item_fifo.get(mstr_seq_item);
       sample_mstr_seq_item();
    end
    
    // 'slv' sequence item coverage
    forever begin
       slv_seq_item_fifo.get(slv_seq_item);
       sample_slv_seq_item();
    end
    
    // 'mstr' monitored transaction coverage
    forever begin
       mstr_mon_trn_fifo.get(mstr_mon_trn);
       sample_mstr_mon_trn();
    end
    
    // 'slv' monitored transaction coverage
    forever begin
       slv_mon_trn_fifo.get(slv_mon_trn);
       sample_slv_mon_trn();
    end
  join_none
   
endtask : run_phase


function void uvme_obi_st_cov_model_c::sample_cfg();
   
  obi_st_cfg_cg.sample();
   
endfunction : sample_cfg


function void uvme_obi_st_cov_model_c::sample_cntxt();
   
   obi_st_cntxt_cg.sample();
   
endfunction : sample_cntxt


function void uvme_obi_st_cov_model_c::sample_mstr_seq_item();
   
   obi_st_mstr_seq_item_cg.sample();
   
endfunction : sample_mstr_seq_item


function void uvme_obi_st_cov_model_c::sample_slv_seq_item();
   
   obi_st_slv_seq_item_cg.sample();
   
endfunction : sample_slv_seq_item


function void uvme_obi_st_cov_model_c::sample_mstr_mon_trn();
   
   obi_st_mstr_mon_trn_cg.sample();
   
endfunction : sample_mstr_mon_trn


function void uvme_obi_st_cov_model_c::sample_slv_mon_trn();
   
   obi_st_slv_mon_trn_cg.sample();
   
endfunction : sample_slv_mon_trn


`endif // __UVME_OBI_ST_COV_MODEL_SV__
