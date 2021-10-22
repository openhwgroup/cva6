// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVME_CV32E40P_COV_MODEL_SV__
`define __UVME_CV32E40P_COV_MODEL_SV__


/**
 * Component encapsulating CV32E40P environment's functional coverage model.
 */
class uvme_cv32e40p_cov_model_c extends uvm_component;
   
   // Objects
   uvme_cv32e40p_cfg_c    cfg;
   uvme_cv32e40p_cntxt_c  cntxt;

   uvme_rv32isa_covg   isa_covg;   
   uvme_interrupt_covg interrupt_covg;
   uvme_debug_covg debug_covg;

   `uvm_component_utils_begin(uvme_cv32e40p_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
      
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40p_cov_model", uvm_component parent=null);
   
   /**
    * Ensures cfg & cntxt handles are not null.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Connects ISA coverage model to interrupt coverage model
    */
   extern virtual function void connect_phase(uvm_phase phase);

   /**
    * Describe uvme_cv32e40p_cov_model_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvme_cv32e40p_cov_model_c::sample_cfg()
    */
   extern virtual function void sample_cfg();
   
   /**
    * TODO Describe uvme_cv32e40p_cov_model_c::sample_cntxt()
    */
   extern virtual function void sample_cntxt();
   
   // TODO Add coverage functions to uvme_cv32e40p_cov_model_c
   //      Ex: /**
   //           * Samples trn via debug_cg
   //           */
   //          extern function void sample_debug();
   
endclass : uvme_cv32e40p_cov_model_c


function uvme_cv32e40p_cov_model_c::new(string name="uvme_cv32e40p_cov_model", uvm_component parent=null);
   
   super.new(name, parent);
   
   // TODO Create coverage groups for uvme_cv32e40p_cov_model_c
   //      Ex: debug_cg = new();
   
endfunction : new

function void uvme_cv32e40p_cov_model_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvme_cv32e40p_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvme_cv32e40p_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   isa_covg = uvme_rv32isa_covg::type_id::create("isa_covg", this);
   uvm_config_db#(uvme_cv32e40p_cntxt_c)::set(this, "isa_covg", "cntxt", cntxt);
   
   interrupt_covg = uvme_interrupt_covg::type_id::create("interrupt_covg", this);
   uvm_config_db#(uvme_cv32e40p_cntxt_c)::set(this, "interrupt_covg", "cntxt", cntxt);

   debug_covg = uvme_debug_covg::type_id::create("debug_covg", this);
   uvm_config_db#(uvme_cv32e40p_cntxt_c)::set(this, "debug_covg", "cntxt", cntxt);
   
endfunction : build_phase

function void uvme_cv32e40p_cov_model_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);

   isa_covg.ap.connect(interrupt_covg.rv32isa_export);
endfunction : connect_phase

task uvme_cv32e40p_cov_model_c::run_phase(uvm_phase phase);
   
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
      
      // TODO Implement uvme_cv32e40p_cov_model_c::run_phase()
      //      Ex: forever begin
      //             debug_fifo.get(debug_trn);
      //             sample_debug();
      //          end
   join_none
   
endtask : run_phase


function void uvme_cv32e40p_cov_model_c::sample_cfg();
   
   // TODO Implement uvme_cv32e40p_cov_model_c::sample_cfg();
   //      Ex: cv32e40p_cfg_cg.sample();
   
endfunction : sample_cfg


function void uvme_cv32e40p_cov_model_c::sample_cntxt();
   
   // TODO Implement uvme_cv32e40p_cov_model_c::sample_cntxt();
   //      Ex: cv32e40p_cntxt_cg.sample();
   
endfunction : sample_cntxt



`endif // __UVME_CV32E40P_COV_MODEL_SV__
