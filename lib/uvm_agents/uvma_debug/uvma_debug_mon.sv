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


`ifndef __UVMA_DEBUG_MON_SV__
`define __UVMA_DEBUG_MON_SV__


/**
 * Component sampling transactions from a Debug virtual interface
 * (uvma_debug_if).
 */
class uvma_debug_mon_c extends uvm_monitor;
   
   // Objects
   uvma_debug_cfg_c    cfg;
   uvma_debug_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_debug_mon_trn_c)  ap;
   
   
   `uvm_component_utils_begin(uvma_debug_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_debug_mon", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * Updates the context's reset state.
    */
   extern virtual task observe_reset();
   
   /**
    * Called by run_phase() while agent is in pre-reset state.
    */
   extern virtual task mon_pre_reset(uvm_phase phase);
   
   /**
    * Called by run_phase() while agent is in reset state.
    */
   extern virtual task mon_in_reset(uvm_phase phase);
   
   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern virtual task mon_post_reset(uvm_phase phase);
   
   /**
    * Creates trn by sampling the virtual interface's (cntxt.vif) signals.
    */
   extern virtual task sample_trn(output uvma_debug_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_debug_mon_c::process_trn()
    */
   extern virtual function void process_trn(ref uvma_debug_mon_trn_c trn);
   
endclass : uvma_debug_mon_c


`pragma protect begin


function uvma_debug_mon_c::new(string name="uvma_debug_mon", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_debug_mon_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_debug_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_debug_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   ap = new("ap", this);
  
endfunction : build_phase


task uvma_debug_mon_c::observe_reset();
   
   // TODO Implement uvma_debug_mon_c::observe_reset()
   //      Ex: forever begin
   //             wait (cntxt.vif.reset == 1);
   //             cntxt.reset_state = UVMA_RESET_STATE_IN_RESET;
   //             wait (cntxt.vif.reset == 0);
   //             cntxt.reset_state = UVMA_RESET_STATE_POST_RESET;
   //          end
   
   // WARNING If no time is consumed by this task, a zero-delay oscillation loop will occur and stall simulation
   
endtask : observe_reset


task uvma_debug_mon_c::mon_pre_reset(uvm_phase phase);
   
   // TODO Implement uvma_debug_mon_c::mon_pre_reset()
   //      Ex: @(cntxt.vif.mon_cb);
   
   // WARNING If no time is consumed by this task, a zero-delay oscillation loop will occur and stall simulation
   
endtask : mon_pre_reset


task uvma_debug_mon_c::mon_in_reset(uvm_phase phase);
   
   // TODO Implement uvma_debug_mon_c::mon_in_reset()
   //      Ex: @(cntxt.vif.mon_cb);
   
   // WARNING If no time is consumed by this task, a zero-delay oscillation loop will occur and stall simulation
   
endtask : mon_in_reset


task uvma_debug_mon_c::mon_post_reset(uvm_phase phase);
   
   uvma_debug_mon_trn_c  trn;
   
   sample_trn (trn);
   process_trn(trn);
   ap.write   (trn);
   
   `uvml_hrtbt()
   
endtask : mon_post_reset


task uvma_debug_mon_c::sample_trn(output uvma_debug_mon_trn_c trn);
   
   bit  sampled_trn = 0;
   
   trn = uvma_debug_mon_trn_c::type_id::create("trn");
   
   do begin
      @(cntxt.vif.mon_cb);
      
      // TODO Sample trn from vif
      //      Ex: if (cntxt.vif.reset == 0) begin
      //             if (cntxt.vif.mon_cb.enable) begin
      //                sampled_trn   = 1;
      //                trn.abc       = cntxt.vif.mon_cb.abc;
      //                trn.xyz       = cntxt.vif.mon_cb.xyz;
      //                trn.timestamp = $realtime();
      //             end
      //          end
      
      // WARNING If no time is consumed by this loop, a zero-delay oscillation loop will occur and stall simulation
   end while (!sampled_trn);
   
endtask : sample_trn


function void uvma_debug_mon_c::process_trn(ref uvma_debug_mon_trn_c trn);
   
   // TODO Implement uvma_debug_mon_c::process_trn()
   
endfunction : process_trn


`pragma protect end


`endif // __UVMA_DEBUG_MON_SV__
