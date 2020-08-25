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


`ifndef __UVMA_INTERRUPT_MON_SV__
`define __UVMA_INTERRUPT_MON_SV__


/**
 * Component sampling transactions from a Clock & Reset virtual interface
 * (uvma_interrupt_if).
 */
class uvma_interrupt_mon_c extends uvm_monitor;
   
   // Objects
   uvma_interrupt_cfg_c    cfg;
   uvma_interrupt_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_interrupt_mon_trn_c)  ap;   
   
   `uvm_component_utils_begin(uvma_interrupt_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_mon", uvm_component parent=null);
   
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
    * Publish a monitor transactin when interrupt is taken.
    */
   extern virtual task monitor_irq();

endclass : uvma_interrupt_mon_c

function uvma_interrupt_mon_c::new(string name="uvma_interrupt_mon", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_interrupt_mon_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_interrupt_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_interrupt_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   ap = new("ap", this);
  
endfunction : build_phase

task uvma_interrupt_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
      
   if (cfg.enabled) begin
      while (1) begin
         wait (cntxt.vif.reset_n === 1'b0);
         wait (cntxt.vif.reset_n === 1'b1);
         
         fork begin
            fork
               monitor_irq();
            join_none

            wait (cntxt.vif.reset_n === 1'b0);
            
            disable fork;
         end
         join 
      end
   end   
endtask : run_phase

task uvma_interrupt_mon_c::monitor_irq();
   while(1) begin
      @(cntxt.vif.mon_cb);

      if (cntxt.vif.mon_cb.irq_ack) begin
         uvma_interrupt_mon_trn_c mon_trn = uvma_interrupt_mon_trn_c::type_id::create("mon_irq_trn");
         mon_trn.action = UVMA_INTERRUPT_MON_ACTION_IRQ;
         mon_trn.id = cntxt.vif.mon_cb.irq_id;
         ap.write(mon_trn);
      end
   end
endtask : monitor_irq


`endif // __UVMA_INTERRUPT_MON_SV__
