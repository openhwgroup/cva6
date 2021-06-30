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


`ifndef __UVMA_CORE_CNTRL_AGENT_SV__
`define __UVMA_CORE_CNTRL_AGENT_SV__

/**
 * Virtual base class agent for Core Control
 * Encapsulates:
 * - Paraameter sampling
 * - Bootstrap pin randomization and driving
 * - Core configuration and randomization
 */
virtual class uvma_core_cntrl_agent_c extends uvm_agent;
   
   // Objects
   uvma_core_cntrl_cfg_c    cfg;
   uvma_core_cntrl_cntxt_c  cntxt;

   // Components   
   uvma_core_cntrl_sqr_c    sequencer;
   uvma_core_cntrl_drv_c    driver;   

   `uvm_field_utils_begin(uvma_core_cntrl_agent_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_field_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_core_cntrl_agent", uvm_component parent=null);
   
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
   
endclass : uvma_core_cntrl_agent_c


function uvma_core_cntrl_agent_c::new(string name="uvma_core_cntrl_agent", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new

function void uvma_core_cntrl_agent_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   get_and_set_cfg  ();
   get_and_set_cntxt();
   retrieve_vif     ();
   create_components();

endfunction : build_phase

function void uvma_core_cntrl_agent_c::connect_phase(uvm_phase phase);
   
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

task uvma_core_cntrl_agent_c::run_phase(uvm_phase phase);

endtask : run_phase

function void uvma_core_cntrl_agent_c::retrieve_vif();

endfunction : retrieve_vif

function void uvma_core_cntrl_agent_c::get_and_set_cfg();
   
   if (uvm_config_db#(uvma_core_cntrl_cfg_c)::get(this, "", "cfg", cfg)) begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "*", "cfg", cfg);
   end
   else begin
      `uvm_fatal("CFG", $sformatf("%s: Could not find configuration handle", this.get_full_name()));
   end
   
endfunction : get_and_set_cfg


function void uvma_core_cntrl_agent_c::get_and_set_cntxt();
   
   if (uvm_config_db#(uvma_core_cntrl_cntxt_c)::get(this, "", "cntxt", cntxt)) begin
      uvm_config_db#(uvma_core_cntrl_cntxt_c)::set(this, "*", "cntxt", cntxt);
   end
   else begin
      `uvm_fatal("CNTXT", $sformatf("%s: Could not find context handle", this.get_full_name()));
   end
   
endfunction : get_and_set_cntxt


function void uvma_core_cntrl_agent_c::create_components();

   if (cfg.is_active == UVM_ACTIVE) begin
      sequencer = uvma_core_cntrl_sqr_c::type_id::create("sequencer", this);
      driver = uvma_core_cntrl_drv_c::type_id::create("driver", this);
   end

endfunction : create_components


function void uvma_core_cntrl_agent_c::connect_sequencer_and_driver();

   if (cfg.is_active == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);      
   end

endfunction : connect_sequencer_and_driver


function void uvma_core_cntrl_agent_c::connect_analysis_ports();
         
endfunction : connect_analysis_ports


function void uvma_core_cntrl_agent_c::connect_cov_model();
      
endfunction : connect_cov_model


function void uvma_core_cntrl_agent_c::connect_trn_loggers();
   
endfunction : connect_trn_loggers


`endif // __UVMA_CORE_CNTRL_AGENT_SV__
