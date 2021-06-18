// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_RVVI_STATE_MON_SV__
`define __UVMA_RVVI_STATE_MON_SV__


/**
 * Component sampling transactions from the RVVI state interface
 * (rvvi_state4if).
 */
class uvma_rvvi_state_mon_c#(int ILEN=DEFAULT_ILEN,
                             int XLEN=DEFAULT_XLEN) extends uvm_monitor;
   
   // Objects   
   uvma_rvvi_cfg_c#(ILEN,XLEN)    cfg;
   uvma_rvvi_cntxt_c#(ILEN,XLEN)  cntxt;
   
   // State
   bit[XLEN-1:0]  last_x[32];
   int unsigned   next_order;

   // TLM
   uvm_analysis_port#(uvma_rvvi_state_seq_item_c#(ILEN,XLEN))  ap;   
   
   string log_tag = "RVVIMONLOG";

   `uvm_component_utils_begin(uvma_rvvi_state_mon_c)      
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_state_mon", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * 1. Resets initial monitor state
    */
   extern virtual task reset_phase(uvm_phase phase);

   /**
    * Oversees monitoring via monitor_clk() and monitor_reset() tasks in parallel
    * forks.
    */
   extern virtual task run_phase(uvm_phase phase);
      
   /**
    * Monitor the state interface
    */
   extern virtual task monitor_rvvi_state();

   /**
    * Reset monitor state
    */
    extern virtual function void reset_state();
endclass : uvma_rvvi_state_mon_c

function uvma_rvvi_state_mon_c::new(string name="uvma_rvvi_state_mon", uvm_component parent=null);
   
   super.new(name, parent);
   
   // Assume that all registers reset from 0
   foreach (last_x[i])
      last_x[i] = 0;
endfunction : new


function void uvma_rvvi_state_mon_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);

   if ($test$plusargs("log_rvvi"))
      set_report_id_verbosity(log_tag, UVM_HIGH);

   void'(uvm_config_db#(uvma_rvvi_cfg_c#(ILEN,XLEN))::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_rvvi_cntxt_c#(ILEN,XLEN))::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   ap = new("ap", this);
  
endfunction : build_phase

task uvma_rvvi_state_mon_c::reset_phase(uvm_phase phase);
   reset_state();
endtask : reset_phase

task uvma_rvvi_state_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
      
   if (cfg.enabled) begin      
      // Note: no concept of reset on RVVI currently, so simple fork of the monitor thread
      fork
         monitor_rvvi_state();
      join_none      
   end
endtask : run_phase

function void uvma_rvvi_state_mon_c::reset_state();
   // Assume all GPRs are reset
   foreach (last_x[i]) 
      last_x[i] = 0;
endfunction : reset_state

task uvma_rvvi_state_mon_c::monitor_rvvi_state();
   while(1) begin
      uvma_rvvi_state_seq_item_c#(ILEN,XLEN) mon_trn;

      @(cntxt.state_vif.notify);      

      mon_trn = uvma_rvvi_state_seq_item_c#(ILEN,XLEN)::type_id::create("rvvi_state_mon_trn");
      
      mon_trn.trap     = cntxt.state_vif.trap;
      mon_trn.halt     = cntxt.state_vif.halt;
      mon_trn.intr     = cntxt.state_vif.intr;
      mon_trn.valid    = cntxt.state_vif.valid;
      mon_trn.order    = cntxt.state_vif.order;
      mon_trn.insn     = cntxt.state_vif.insn;
      mon_trn.isize    = cntxt.state_vif.isize;
      $cast(mon_trn.mode, cntxt.state_vif.mode);
      mon_trn.ixl      = cntxt.state_vif.ixl;
      mon_trn.pc       = cntxt.state_vif.pc;
      mon_trn.pcnext   = cntxt.state_vif.pcnext;
 
      foreach (mon_trn.x[i])
         mon_trn.x[i] = cntxt.state_vif.x[i];

      // Detect any changed GPRs         
      for (int i = 0; i < 32; i++) begin
         if (cntxt.state_vif.x[i] != last_x[i]) begin
            mon_trn.gpr_update[i] = cntxt.state_vif.x[i];
            last_x[i] = cntxt.state_vif.x[i];
         end
      end
      
      `uvm_info(log_tag, $sformatf("%s", mon_trn.convert2string()), UVM_HIGH);

      ap.write(mon_trn);
   end
endtask : monitor_rvvi_state

`endif // __UVMA_RVVI_STATE_MON_SV__
