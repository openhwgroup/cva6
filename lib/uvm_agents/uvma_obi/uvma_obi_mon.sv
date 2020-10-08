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


`ifndef __UVMA_OBI_MON_SV__
`define __UVMA_OBI_MON_SV__


/**
 * Component sampling transactions from a Clock & Reset virtual interface
 * (uvma_obi_if).
 */
class uvma_obi_mon_c extends uvm_monitor;
   
   // Objects
   uvma_obi_cfg_c    cfg;
   uvma_obi_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_obi_mon_trn_c)  ap;   
   
   // Internal data structures
   uvma_obi_mon_trn_c    mon_trn_addr_q[$];

   `uvm_component_utils_begin(uvma_obi_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mon", uvm_component parent=null);
   
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
    * Monitor the req_gnt interface
    */
   extern virtual task monitor_req();

   /**
    * Monitor the rvalid response interface
    */
   extern virtual task monitor_resp();

endclass : uvma_obi_mon_c

function uvma_obi_mon_c::new(string name="uvma_obi_mon", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_mon_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   ap = new("ap", this);
  
endfunction : build_phase

task uvma_obi_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
      
   if (cfg.enabled) begin
      while (1) begin
         wait (cntxt.vif.reset_n === 1'b0);
         wait (cntxt.vif.reset_n === 1'b1);
         
         fork begin
            fork
               monitor_req;
               monitor_resp();
            join_none

            wait (cntxt.vif.reset_n === 1'b0);
            
            disable fork;
            mon_trn_addr_q.delete();
         end
         join 
      end
   end   
endtask : run_phase

task uvma_obi_mon_c::monitor_req();
   while(1) begin
      @(cntxt.vif.mon_cb);

      if (cntxt.vif.mon_cb.req && cntxt.vif.mon_cb.gnt) begin
         uvma_obi_mon_trn_c mon_trn = uvma_obi_mon_trn_c::type_id::create("obi_mon_trn");
         mon_trn.addr  = cntxt.vif.mon_cb.addr;
         mon_trn.be    = cntxt.vif.mon_cb.be;
         mon_trn.we    = cntxt.vif.mon_cb.we;
         if (mon_trn.we)
            mon_trn.data = cntxt.vif.mon_cb.wdata;

         mon_trn_addr_q.push_back(mon_trn);
      end

      // if (cntxt.vif.mon_cb.irq_ack) begin
      //    uvma_obi_mon_trn_c mon_trn = uvma_obi_mon_trn_c::type_id::create("mon_irq_trn");
      //    mon_trn.action = UVMA_OBI_MON_ACTION_IRQ;
      //    mon_trn.id = cntxt.vif.mon_cb.irq_id;
      //    ap.write(mon_trn);
      // end
   end
endtask : monitor_req

task uvma_obi_mon_c::monitor_resp();
   while(1) begin
      @(cntxt.vif.mon_cb);

      if (cntxt.vif.mon_cb.rvalid && cntxt.vif.mon_cb.rready) begin
         uvma_obi_mon_trn_c mon_trn;

         if (mon_trn_addr_q.size() == 0) begin
            `uvm_fatal("OBIMON", $sformatf("%s Received response without address", this.get_full_name()))
         end

         mon_trn = mon_trn_addr_q.pop_front();
         
         if (!mon_trn.we)
            mon_trn.data = cntxt.vif.mon_cb.rdata;
         
         ap.write(mon_trn);
      end
   end
endtask : monitor_resp

`endif // __UVMA_OBI_MON_SV__
