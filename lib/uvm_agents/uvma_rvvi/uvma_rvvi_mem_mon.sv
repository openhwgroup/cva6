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


`ifndef __UVMA_RVFI_MEM_MON_SV__
`define __UVMA_RVFI_MEM_MON_SV__


/**
 * Component sampling transactions from a Clock & Reset virtual interface
 * (uvma_rvfi_mem_if).
 */
class uvma_rvfi_mem_mon_c extends uvm_monitor;
   
   // Objects   
   uvma_rvfi_cfg_c    cfg;
   uvma_rvfi_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_rvfi_mem_seq_item_c)  ap;   
   
   `uvm_component_utils_begin(uvma_rvfi_mem_mon_c)      
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvfi_mem_mon", uvm_component parent=null);
   
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
    * Monitor the memuction interface
    */
   extern virtual task monitor_rvfi_mem();

endclass : uvma_rvfi_mem_mon_c

function uvma_rvfi_mem_mon_c::new(string name="uvma_rvfi_mem_mon", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_rvfi_mem_mon_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_rvfi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_rvfi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   ap = new("ap", this);
  
endfunction : build_phase

task uvma_rvfi_mem_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
      
   if (cfg.enabled) begin
      while (1) begin
         wait (cntxt.mem_vif.reset_n === 1'b0);
         wait (cntxt.mem_vif.reset_n === 1'b1);
         
         fork begin
            fork
               monitor_rvfi_mem();
            join_none

            wait (cntxt.mem_vif.reset_n === 1'b0);
            
            disable fork;            
         end
         join 
      end
   end   
endtask : run_phase

task uvma_rvfi_mem_mon_c::monitor_rvfi_mem();
   while(1) begin
      @(cntxt.mem_vif.mon_cb);
      
      if (cntxt.mem_vif.mon_cb.mem_rvalid || 
          cntxt.mem_vif.mon_cb.mem_wvalid) begin
         uvma_rvfi_mem_seq_item_c mon_trn = uvma_rvfi_mem_seq_item_c::type_id::create("rvfi_mem_mon_trn");

         mon_trn.mem_addr = cntxt.mem_vif.mon_cb.mem_addr;

         mon_trn.mem_rdata = cntxt.mem_vif.mon_cb.mem_rdata;
         mon_trn.mem_rmask = cntxt.mem_vif.mon_cb.mem_rmask;
         mon_trn.mem_rvalid = cntxt.mem_vif.mon_cb.mem_rvalid;

         mon_trn.mem_wdata = cntxt.mem_vif.mon_cb.mem_wdata;
         mon_trn.mem_wmask = cntxt.mem_vif.mon_cb.mem_wmask;
         mon_trn.mem_wvalid = cntxt.mem_vif.mon_cb.mem_wvalid;

         ap.write(mon_trn);
      end      
   end
endtask : monitor_rvfi_mem

`endif // __UVMA_RVFI_MEM_MON_SV__
