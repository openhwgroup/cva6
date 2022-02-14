// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_AGENT_SV__
`define __UVMA_CVXIF_AGENT_SV__


class uvma_cvxif_agent_c extends uvm_agent;

   // Components
   uvma_cvxif_mon_c    monitor;
   uvma_cvxif_sqr_c    sequencer;
   uvma_cvxif_drv_c    driver;

   // Objects
   uvma_cvxif_cfg_c    cfg;

   virtual uvma_cvxif_intf cvxif_vif;

   string info_tag = "CVXIF_AGENT";

   `uvm_component_utils_begin(uvma_cvxif_agent_c)
      `uvm_field_object(cfg, UVM_DEFAULT)
   `uvm_component_utils_end
   /**
    * Default constructor.
   */
   extern function new(string name="uvma_cvxif_agent", uvm_component parent=null);

   /**
    * 1. Ensures vif handle is not null
    * 2. Builds all components
   */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Links agent's analysis ports to sub-components'
    */
   extern virtual function void connect_phase(uvm_phase phase);

   extern virtual function void get_and_set_cfg();

   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this
    * agent.
   */
   extern function void retrieve_vif();

   /**
    * Creates sub-components.
    */
   extern function void create_components();

   /**
    * Connects sequencer and driver's TLM port(s).
    */
   extern function void connect_sequencer_and_driver();

   /**
    * Connects agent's TLM ports to driver's and monitor's.
   */
   extern function void connect_analysis_ports();

endclass : uvma_cvxif_agent_c

function uvma_cvxif_agent_c::new(string name="uvma_cvxif_agent", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvma_cvxif_agent_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   get_and_set_cfg  ();
   retrieve_vif     ();
   create_components();

endfunction : build_phase

function void uvma_cvxif_agent_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

   connect_analysis_ports();
   connect_sequencer_and_driver();

endfunction: connect_phase

function void uvma_cvxif_agent_c::get_and_set_cfg();

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_cvxif_cfg_c)::set(this, "*", "cfg", cfg);
   end

endfunction : get_and_set_cfg

function void uvma_cvxif_agent_c::retrieve_vif();

   if (!uvm_config_db#(virtual uvma_cvxif_intf)::get(this, "", "cvxif_vif", cvxif_vif)) begin
      `uvm_fatal(info_tag, $sformatf("Could not find vif handle in uvm_config_db"))
   end

endfunction : retrieve_vif

function void uvma_cvxif_agent_c::create_components();

   monitor   = uvma_cvxif_mon_c ::type_id::create("monitor"  , this);
   sequencer = uvma_cvxif_sqr_c ::type_id::create("sequencer", this);
   driver    = uvma_cvxif_drv_c ::type_id::create("driver"   , this);

endfunction : create_components

function void uvma_cvxif_agent_c::connect_sequencer_and_driver();

   driver.seq_item_port.connect(sequencer.seq_item_export);

endfunction : connect_sequencer_and_driver

function void uvma_cvxif_agent_c::connect_analysis_ports();

   monitor.req_ap.connect(sequencer.mm_req_fifo.analysis_export);

endfunction : connect_analysis_ports


`endif // __UVMA_CVXIF_AGENT_SV__
