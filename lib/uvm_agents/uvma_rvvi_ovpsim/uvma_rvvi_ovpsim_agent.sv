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


`ifndef __UVMA_RVVI_OVPSIM_AGENT_SV__
`define __UVMA_RVVI_OVPSIM_AGENT_SV__

/**
 * Top-level component that encapsulates, builds and connects all others.
 * Capable of driving/monitoring Clock & Reset interface.
 */
class uvma_rvvi_ovpsim_agent_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN, 
                                int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN) extends uvma_rvvi_agent_c#(ILEN,XLEN);
   
   `uvm_component_param_utils_begin(uvma_rvvi_ovpsim_agent_c#(ILEN,XLEN))
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_ovpsim_agent", uvm_component parent=null);

   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this
    * agent.
    */
   extern virtual function void retrieve_vif();   
   /**
    * Creates sub-components.
    */
   extern virtual function void create_components();

   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern virtual function void get_and_set_cntxt();

   /**
    * Provide sequencer for RVVI OVPSIM driver to manage clocks for step and compare
    */
   extern function void set_clknrst_sequencer(uvma_clknrst_sqr_c clknrst_sequencer);

   /**
    *  run_phase will kick off the control sequence that runs the duration
    *  of the simulation (if this agent is active)
    */
   extern virtual task run_phase(uvm_phase phase);

endclass : uvma_rvvi_ovpsim_agent_c


function uvma_rvvi_ovpsim_agent_c::new(string name="uvma_rvvi_ovpsim_agent", uvm_component parent=null);
   
   super.new(name, parent);
   
   log_tag = "RVVIOVPAGT";

endfunction : new

function void uvma_rvvi_ovpsim_agent_c::get_and_set_cntxt();
   
   super.get_and_set_cntxt();
   // void'(uvm_config_db#(uvma_rvvi_cntxt_c#(ILEN,XLEN))::get(this, "", "cntxt", cntxt));
   // if (!cntxt) begin
   //    `uvm_fatal("RVVIOVPAGT", "Context handle is null");      
   // end   
   
endfunction : get_and_set_cntxt

function void uvma_rvvi_ovpsim_agent_c::set_clknrst_sequencer(uvma_clknrst_sqr_c clknrst_sequencer);

   uvma_rvvi_ovpsim_drv_c#(ILEN,XLEN) rvvi_ovpsim_driver;

   // Cast into the OVPSIM context to get access to the BUS interface
   if (!$cast(rvvi_ovpsim_driver, driver)) begin
      `uvm_fatal(log_tag, "Failed to cast RVVI driver to RVVI ovpsim_driver");
   end
   rvvi_ovpsim_driver.clknrst_sequencer = clknrst_sequencer;

endfunction : set_clknrst_sequencer

function void uvma_rvvi_ovpsim_agent_c::retrieve_vif();

   uvma_rvvi_ovpsim_cntxt_c#(ILEN,XLEN) rvvi_ovpsim_cntxt;

   // Cast into the OVPSIM context to get access to the BUS interface
   if (!$cast(rvvi_ovpsim_cntxt, cntxt)) begin
      `uvm_fatal(log_tag, "Failed to cast RVVI cntxt to RVVI ovpsim_cntxt");
   end

   super.retrieve_vif();
   
   // OVPSIM BUS VIF : FIXME:strichmo:would be ideal to incorporate into common rvvi 
   if (!uvm_config_db#(virtual BUS)::get(this, "", $sformatf("ovpsim_bus_vif"), rvvi_ovpsim_cntxt.ovpsim_bus_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", 
                                    $typename(rvvi_ovpsim_cntxt.ovpsim_bus_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", 
                                 $typename(rvvi_ovpsim_cntxt.ovpsim_bus_vif)), UVM_DEBUG)
   end
endfunction : retrieve_vif


function void uvma_rvvi_ovpsim_agent_c::create_components();

   state_monitor   = uvma_rvvi_ovpsim_state_mon_c#(ILEN,XLEN)::type_id::create("state_monitor"  , this);
   mon_trn_logger  = uvma_rvvi_mon_trn_logger_c#(ILEN,XLEN)::type_id::create("mon_trn_logger" , this);
   
   if (cfg.is_active == UVM_ACTIVE) begin
      sequencer = uvma_rvvi_sqr_c#(ILEN,XLEN)::type_id::create("sequencer", this);
      driver = uvma_rvvi_ovpsim_drv_c#(ILEN,XLEN)::type_id::create("driver", this);
   end

endfunction : create_components

task uvma_rvvi_ovpsim_agent_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   if (cfg.is_active == UVM_ACTIVE) begin
      uvma_rvvi_ovpsim_control_seq_c#(ILEN,XLEN) control_seq = uvma_rvvi_ovpsim_control_seq_c#(ILEN, XLEN)::type_id::create("control_seq");

      `uvm_info("RVVIOVPAGT", "Starting the RVVI control sequence...", UVM_LOW);
      fork
         control_seq.start(sequencer);
      join_none
   end

endtask : run_phase



`endif // __UVMA_RVVI_OVPSIM_AGENT_SV__
