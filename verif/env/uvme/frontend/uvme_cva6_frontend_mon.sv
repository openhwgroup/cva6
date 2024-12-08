// Copyright 2024 Thales DIS SAS
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
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVME_CVA6_FRONTEND_MON_SV__
`define __UVME_CVA6_FRONTEND_MON_SV__


// Frontend transaction
class uvme_cva6_frontend_transaction_c extends uvm_sequence_item;

   logic  flush;
   logic  flush_bp;

   uvme_frontend_icache_req_t   icache_req;
   uvme_frontend_icache_rsp_t   icache_rsp;

   uvme_frontend_bp_resolve_t  resolve_branch;

   logic             fetch_valid[RTLCVA6Cfg.NrIssuePorts];
   logic             fetch_ready[RTLCVA6Cfg.NrIssuePorts];
   uvme_frontend_fetched_data_t  fetch_instr[RTLCVA6Cfg.NrIssuePorts];

   logic                      boot_valid;

   logic                      eret;
   logic[RTLCVA6Cfg.VLEN-1:0] epc;

   logic                      ex_valid;
   logic                      halt;
   logic[RTLCVA6Cfg.VLEN-1:0] trap_vector_base;

   logic                      set_pc_commit;
   logic[RTLCVA6Cfg.VLEN-1:0] pc_commit;

   logic                      set_debug_pc;

   `uvm_object_utils_begin(uvme_cva6_frontend_transaction_c)
        `uvm_field_int        (                               flush         , UVM_DEFAULT | UVM_BIN)
        `uvm_field_int        (                               flush_bp      , UVM_DEFAULT | UVM_BIN)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   function new(string name="uvme_cva6_frontend_transaction");
         super.new(name);
   endfunction

endclass : uvme_cva6_frontend_transaction_c


// Frontend Monitor
// Instantiate a virtual interface of the frontend
// Capture all the necessary signals in a frontend transaction and send them through an analysis port.
class uvme_cva6_frontend_mon_c extends uvm_monitor;

   `uvm_component_utils(uvme_cva6_frontend_mon_c)

   // Objects
   uvme_cva6_cfg_c    cfg;

   // Analysis Ports
   uvm_analysis_port #(uvme_cva6_frontend_transaction_c) frontend_packets_collected;

   // Handle to agent switch interface
   virtual uvmt_frontend_intf  frontend_vif;

   event reset_asserted ;
   event reset_deasserted ;

   /**
    *  Constructor
    */
   function new(string name="uvme_cva6_frontend_mon", uvm_component parent=null);
         super.new(name, parent);
   endfunction

   /**
    *  Build Phase
    */
   function void build_phase(uvm_phase phase);

      super.build_phase(phase);

      // Instantiation of the uvm_analysis_port
      frontend_packets_collected      = new("frontend_packets_collected" , this) ;

      if (!uvm_config_db#(virtual uvmt_frontend_intf)::get(this, "", "cva6_frontend_bus", frontend_vif)) begin
         `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(frontend_vif)))
      end
      else begin
         `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(frontend_vif)), UVM_DEBUG)
      end

      void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
      if (!cfg)
         `uvm_fatal("CFG", "Configuration handle is null")

   endfunction : build_phase

   /**
    *  Pre reset phase
    */
   virtual task pre_reset_phase(uvm_phase phase);
      -> reset_asserted;
   endtask : pre_reset_phase

   /**
    *  Reset phase
    */
   virtual task reset_phase(uvm_phase phase);
      super.reset_phase(phase);
   endtask : reset_phase

   /**
    * Post reset phase
    */
   virtual task post_reset_phase(uvm_phase phase);
      -> reset_deasserted;
   endtask : post_reset_phase

   /**
    * Run Phase
    */
   task run_phase(uvm_phase phase);
      forever begin
         @(reset_deasserted);
         fork
            receive_frontend_transaction_task(phase);
         join_none
         @(reset_asserted);
         disable fork;
      end
   endtask : run_phase

   /**
    * Task receive frontend request and response
    */
   task receive_frontend_transaction_task(uvm_phase phase);
      uvme_cva6_frontend_transaction_c   frontend_transaction;
      int predict;
      int boot_valid = 1;

      forever begin
         @(posedge frontend_vif.clk);
         frontend_transaction = new();
         frontend_transaction.flush    = frontend_vif.flush_i;
         frontend_transaction.flush_bp = frontend_vif.flush_bp_i;
         frontend_transaction.icache_rsp.req     = frontend_vif.icache_dreq_o.req;
         frontend_transaction.icache_rsp.kill_s1 = frontend_vif.icache_dreq_o.kill_s1;
         frontend_transaction.icache_rsp.kill_s2 = frontend_vif.icache_dreq_o.kill_s2;
         frontend_transaction.icache_rsp.vaddr   = frontend_vif.icache_dreq_o.vaddr;
         frontend_transaction.icache_req.ready   = frontend_vif.icache_dreq_i.ready;
         frontend_transaction.icache_req.valid   = frontend_vif.icache_dreq_i.valid;
         frontend_transaction.icache_req.data    = frontend_vif.icache_dreq_i.data;
         frontend_transaction.icache_req.vaddr   = frontend_vif.icache_dreq_i.vaddr;
         frontend_transaction.resolve_branch     = frontend_vif.resolved_branch_i;
         for(int i = 0; i < RTLCVA6Cfg.NrIssuePorts; i++) begin
            frontend_transaction.fetch_valid[i]                   = frontend_vif.fetch_entry_valid_o[i];
            frontend_transaction.fetch_ready[i]                   = frontend_vif.fetch_entry_ready_i[i];
            frontend_transaction.fetch_instr[i].address           = frontend_vif.fetch_entry_o[i].address;
            frontend_transaction.fetch_instr[i].instruction       = frontend_vif.fetch_entry_o[i].instruction;
            predict = frontend_vif.fetch_entry_o[i].branch_predict.cf;
            frontend_transaction.fetch_instr[i].predict           = predict;
            frontend_transaction.fetch_instr[i].predicted_address = frontend_vif.fetch_entry_o[i].branch_predict.predict_address;
         end
         frontend_transaction.eret             = frontend_vif.eret_i;
         frontend_transaction.epc              = frontend_vif.epc_i;
         frontend_transaction.ex_valid         = frontend_vif.ex_valid_i;
         frontend_transaction.halt             = frontend_vif.halt_i;
         frontend_transaction.trap_vector_base = frontend_vif.trap_vector_base_i;
         frontend_transaction.set_pc_commit    = frontend_vif.set_pc_commit_i;
         frontend_transaction.pc_commit        = frontend_vif.pc_commit_i;
         frontend_transaction.set_debug_pc     = frontend_vif.set_debug_pc_i;
         if(boot_valid == 1) begin
            frontend_transaction.boot_valid = 1;
         end else begin
            frontend_transaction.boot_valid = 0;
         end
         boot_valid = 0;

         frontend_packets_collected.write(frontend_transaction);
      end // forever
   endtask : receive_frontend_transaction_task
endclass : uvme_cva6_frontend_mon_c


`endif // __UVME_CVA6_FRONTEND_MON_SV__
