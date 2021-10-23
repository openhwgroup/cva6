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


`ifndef __UVMA_CLKNRST_MON_SV__
`define __UVMA_CLKNRST_MON_SV__


/**
 * Component sampling transactions from a Clock & Reset virtual interface
 * (uvma_clknrst_if).
 */
class uvma_clknrst_mon_c extends uvm_monitor;
   
   // Objects
   uvma_clknrst_cfg_c    cfg;
   uvma_clknrst_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_clknrst_mon_trn_c)  ap;
   
   
   `uvm_component_utils_begin(uvma_clknrst_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_clknrst_mon", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * Oversees monitoring via monitor_clk() and monitor_reset() tasks in parallel
    * forks.
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Creates trn by sampling the virtual interface's (cntxt.vif) clk signal.
    */
   extern task monitor_clk(output uvma_clknrst_mon_trn_c trn);
   
   /**
    * Creates trn by sampling the virtual interface's (cntxt.vif) reset_n signal.
    */
   extern task monitor_reset(output uvma_clknrst_mon_trn_c trn);
   
   /**
    * Empty, classes extending this monitor can do their intercept here.
    */
   extern function void process_trn(ref uvma_clknrst_mon_trn_c trn);
   
   /**
    * Monitors clock signal for loss of clock, generating a transaction only if
    * and when this is detected.
    */
   extern task monitor_clock_loss(output uvma_clknrst_mon_trn_c trn);
   
   /**
    * Emits a transaction once clock lock has been achieved.
    */
   extern task lock_to_clock(output uvma_clknrst_mon_trn_c trn);
   
endclass : uvma_clknrst_mon_c


function uvma_clknrst_mon_c::new(string name="uvma_clknrst_mon", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_clknrst_mon_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_clknrst_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_clknrst_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   ap = new("ap", this);
  
endfunction : build_phase


task uvma_clknrst_mon_c::run_phase(uvm_phase phase);
   
   uvma_clknrst_mon_trn_c  clk_trn, reset_trn;
   
   super.run_phase(phase);
   
   if (cfg.enabled) begin
      fork
         begin : clk
            forever begin
               monitor_clk(clk_trn);
               `uvml_hrtbt()
               process_trn(clk_trn);
               ap.write   (clk_trn);
            end
         end
         
         begin : reset
            forever begin
               monitor_reset(reset_trn);
               `uvml_hrtbt()
               process_trn  (reset_trn);
               ap.write     (reset_trn);
            end
         end
      join_none
   end
   
endtask : run_phase


task uvma_clknrst_mon_c::monitor_clk(output uvma_clknrst_mon_trn_c trn);
   
   if (cntxt.mon_clk_lock) begin
      monitor_clock_loss(trn);
   end
   else begin
      lock_to_clock(trn);
   end
   
endtask : monitor_clk


task uvma_clknrst_mon_c::monitor_reset(output uvma_clknrst_mon_trn_c trn);
   
   bit  sampled_trn = 0;
   
   trn = uvma_clknrst_mon_trn_c::type_id::create("trn");
   
   do begin
      @(cntxt.vif.reset_n);
      if (cntxt.vif.reset_n !== cntxt.mon_reset_state) begin
         case ({cntxt.mon_reset_state, cntxt.vif.reset_n})
            // 1 -> 0
            2'b10: begin
               cntxt.mon_reset_assert_timestamp = $realtime();
               trn.event_type = UVMA_CLKNRST_MON_TRN_EVENT_RESET_ASSERTED;
               //trn.timestamp  = $realtime();
               trn.__timestamp_start  = $realtime();
               sampled_trn = 1;
            end
            
            // 0 -> 1
            2'b01: begin
               trn.reset_pulse_length = $realtime() - cntxt.mon_reset_assert_timestamp;
               trn.event_type = UVMA_CLKNRST_MON_TRN_EVENT_RESET_DEASSERTED;
               //trn.timestamp  = $realtime();
               trn.__timestamp_end  = $realtime();
               sampled_trn = 1;
            end
            
            2'bX0: begin
               cntxt.mon_reset_assert_timestamp = $realtime();
               trn.event_type = UVMA_CLKNRST_MON_TRN_EVENT_RESET_ASSERTED;
               //trn.timestamp  = $realtime();
               trn.__timestamp_start  = $realtime();
               sampled_trn = 1;
            end
         endcase
         
         cntxt.mon_reset_state = cntxt.vif.reset_n;
      end
   end while (!sampled_trn);
   
endtask : monitor_reset


function void uvma_clknrst_mon_c::process_trn(ref uvma_clknrst_mon_trn_c trn);
   
   // Empty
   
endfunction : process_trn


task uvma_clknrst_mon_c::monitor_clock_loss(output uvma_clknrst_mon_trn_c trn);
   
   trn = uvma_clknrst_mon_trn_c::type_id::create("trn");
   
   forever begin
      @(cntxt.vif.clk);
      // TODO Implement uvma_clknrst_mon_c::monitor_clock_loss()
   end
   
endtask : monitor_clock_loss


task uvma_clknrst_mon_c::lock_to_clock(output uvma_clknrst_mon_trn_c trn);
   
   trn = uvma_clknrst_mon_trn_c::type_id::create("trn");
   
   forever begin
      @(cntxt.vif.clk);
      // TODO Implement uvma_clknrst_mon_c::lock_to_clock()
   end
   
endtask : lock_to_clock


`endif // __UVMA_CLKNRST_MON_SV__
