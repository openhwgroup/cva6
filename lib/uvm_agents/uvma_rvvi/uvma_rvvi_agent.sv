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


`ifndef __UVMA_RVVI_AGENT_SV__
`define __UVMA_RVVI_AGENT_SV__

/**
 * Top-level component that encapsulates, builds and connects all others.
 * Capable of driving/monitoring Clock & Reset interface.
 */
class uvma_rvvi_agent_c#(int ILEN=DEFAULT_ILEN, 
                         int XLEN=DEFAULT_XLEN) extends uvm_agent;
   
   // Objects
   uvma_rvvi_cfg_c#(ILEN,XLEN)   cfg;
   uvma_rvvi_cntxt_c#(ILEN,XLEN) cntxt;
   
   // Components   
   uvma_rvvi_state_mon_c#(ILEN,XLEN)       state_monitor;
   uvma_rvvi_mon_trn_logger_c#(ILEN,XLEN)  mon_trn_logger;
   uvma_rvvi_sqr_c#(ILEN,XLEN)             sequencer;
   uvma_rvvi_drv_c#(ILEN,XLEN)             driver;
   
   // TLM   
   uvm_analysis_port#(uvma_rvvi_state_seq_item_c#(ILEN,XLEN)) state_mon_ap;
   
   string log_tag = "RVVIAGT";

   `uvm_component_param_utils_begin(uvma_rvvi_agent_c#(ILEN,XLEN))
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end  
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_agent", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. Builds all components
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * 1. Links agent's analysis ports to sub-components'
    * 2. Connects coverage models and loggers
    */
   extern virtual function void connect_phase(uvm_phase phase);

   /**
    *  run_phase will kick off the control sequence that runs the duration
    *  of the simulation (if this agent is active)
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
   extern virtual function void get_and_set_cfg();
   
   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern virtual function void get_and_set_cntxt();
   
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
    * Connects sequencer and driver's TLM port(s).
    */
   extern virtual function void connect_sequencer_and_driver();
   
   /**
    * Connects agent's TLM ports to driver's and monitor's.
    */
   extern virtual function void connect_analysis_ports();
   
   /**
    * Connects coverage model to monitor and driver's analysis ports.
    */
   extern virtual function void connect_cov_model();
   
   /**
    * Connects transaction loggers to monitor and driver's analysis ports.
    */
   extern virtual function void connect_trn_loggers();
   
endclass : uvma_rvvi_agent_c


function uvma_rvvi_agent_c::new(string name="uvma_rvvi_agent", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_rvvi_agent_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   get_and_set_cfg  ();
   get_and_set_cntxt();
   retrieve_vif     ();
   create_components();
   
endfunction : build_phase


function void uvma_rvvi_agent_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   connect_sequencer_and_driver();
   connect_analysis_ports();
   
   if (cfg.cov_model_enabled) begin
      connect_cov_model();
   end
   if (cfg.trn_log_enabled) begin
      connect_trn_loggers();
   end
   
endfunction: connect_phase

task uvma_rvvi_agent_c::run_phase(uvm_phase phase);

endtask : run_phase

function void uvma_rvvi_agent_c::get_and_set_cfg();
   
   void'(uvm_config_db#(uvma_rvvi_cfg_c#(ILEN,XLEN))::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_rvvi_cfg_c#(ILEN,XLEN))::set(this, "*", "cfg", cfg);
   end
   
endfunction : get_and_set_cfg


function void uvma_rvvi_agent_c::get_and_set_cntxt();
   
   void'(uvm_config_db#(uvma_rvvi_cntxt_c#(ILEN,XLEN))::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_info("CNTXT", "Context handle is null; creating.", UVM_LOW)
      cntxt = uvma_rvvi_cntxt_c#(ILEN,XLEN)::type_id::create("cntxt");
   end
   uvm_config_db#(uvma_rvvi_cntxt_c#(ILEN,XLEN))::set(this, "*", "cntxt", cntxt);
   
endfunction : get_and_set_cntxt


function void uvma_rvvi_agent_c::retrieve_vif();

   // State monitor
   if (!uvm_config_db#(virtual RVVI_state#(ILEN,XLEN))::get(this, "", $sformatf("state_vif"), cntxt.state_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", 
                                    $typename(cntxt.state_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", 
                                 $typename(cntxt.state_vif)), UVM_DEBUG)
   end

   // Control interface
   if (!uvm_config_db#(virtual RVVI_control)::get(this, "", $sformatf("control_vif"), cntxt.control_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", 
                                    $typename(cntxt.control_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", 
                                 $typename(cntxt.control_vif)), UVM_DEBUG)
   end

endfunction : retrieve_vif


function void uvma_rvvi_agent_c::create_components();

   state_monitor   = uvma_rvvi_state_mon_c#(ILEN,XLEN)     ::type_id::create("state_monitor"  , this);
   mon_trn_logger  = uvma_rvvi_mon_trn_logger_c#(ILEN,XLEN)::type_id::create("mon_trn_logger" , this);
   
   if (cfg.is_active == UVM_ACTIVE) begin
      sequencer = uvma_rvvi_sqr_c#(ILEN,XLEN)::type_id::create("sequencer", this);
   end
endfunction : create_components


function void uvma_rvvi_agent_c::connect_sequencer_and_driver();
   if (cfg.is_active == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);      
   end
endfunction : connect_sequencer_and_driver


function void uvma_rvvi_agent_c::connect_analysis_ports();
      
   state_mon_ap = state_monitor.ap;

endfunction : connect_analysis_ports


function void uvma_rvvi_agent_c::connect_cov_model();
   
   //mon_ap.connect(cov_model.mon_trn_fifo.analysis_export);   
   
endfunction : connect_cov_model


function void uvma_rvvi_agent_c::connect_trn_loggers();
   
   state_mon_ap.connect(mon_trn_logger.state_export);

endfunction : connect_trn_loggers


`endif // __UVMA_RVVI_AGENT_SV__
