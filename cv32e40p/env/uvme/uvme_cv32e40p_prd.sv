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


`ifndef __UVME_CV32E40P_PRD_SV__
`define __UVME_CV32E40P_PRD_SV__


/**
 * Component implementing transaction-based software model of CV32E40P DUT.
 */
class uvme_cv32e40p_prd_c extends uvm_component;
   
   // Objects
   uvme_cv32e40p_cfg_c    cfg;
   uvme_cv32e40p_cntxt_c  cntxt;
   
   // Input TLM
   uvm_analysis_export  #(uvma_clknrst_mon_trn_c)  clknrst_export;
   uvm_tlm_analysis_fifo#(uvma_clknrst_mon_trn_c)  clknrst_fifo;
   //uvm_analysis_export  #(uvma_debug_mon_trn_c)    debug_export;
   //uvm_tlm_analysis_fifo#(uvma_debug_mon_trn_c)    debug_fifo;
   
   // Output TLM
   // TODO Add TLM outputs to uvme_cv32e40p_prd_c
   //      Ex: uvm_analysis_port#(uvma_packet_trn_c)  pkts_out_ap;
   
   
   `uvm_component_utils_begin(uvme_cv32e40p_prd_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40p_prd", uvm_component parent=null);
   
   /**
    * TODO Describe uvme_cv32e40p_prd_c::build_phase()
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvme_cv32e40p_prd_c::connect_phase()
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvme_cv32e40p_prd_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvme_cv32e40p_prd_c::process_clknrst()
    */
   extern task process_clknrst();
   
   /**
    * TODO Describe uvme_cv32e40p_prd_c::process_debug()
    */
   //extern task process_debug();
   
endclass : uvme_cv32e40p_prd_c


function uvme_cv32e40p_prd_c::new(string name="uvme_cv32e40p_prd", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvme_cv32e40p_prd_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvme_cv32e40p_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvme_cv32e40p_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   // Build Input TLM objects
   clknrst_export = new("clknrst_export", this);
   clknrst_fifo   = new("clknrst_fifo"  , this);
   //debug_export = new("debug_export", this);
   //debug_fifo   = new("debug_fifo"  , this);
   
   // Build Output TLM objects
   // TODO Create Output TLM objects for uvme_cv32e40p_prd_c
   //      Ex: pkts_out_ap = new("pkts_out_ap", this);
   
endfunction : build_phase


function void uvme_cv32e40p_prd_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   // Connect TLM objects
   clknrst_export.connect(clknrst_fifo.analysis_export);
   //debug_export.connect(debug_fifo.analysis_export);
   
endfunction: connect_phase


task uvme_cv32e40p_prd_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   fork
      process_clknrst();
      //process_debug();
   join_none
   
endtask: run_phase


task uvme_cv32e40p_prd_c::process_clknrst();
   
   uvma_clknrst_mon_trn_c  clknrst_trn;
   
   forever begin
      clknrst_fifo.get(clknrst_trn);
      
      // TODO Implement uvme_cv32e40p_prd_c::process_clknrst()
   end
   
endtask : process_clknrst


//task uvme_cv32e40p_prd_c::process_debug();
//   
//   uvma_debug_mon_trn_c  debug_trn;
//   
//   forever begin
//      debug_fifo.get(debug_trn);
//      
//      // TODO Implement uvme_cv32e40p_prd_c::process_debug()
//   end
//   
//endtask : process_debug


`endif // __UVME_CV32E40P_PRD_SV__
