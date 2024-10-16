// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_AGENT_SV__
`define __UVMA_INTERRUPT_AGENT_SV__

class uvma_interrupt_agent_c extends uvm_agent;

   // Objects
   uvma_interrupt_cfg_c              cfg;
   uvma_interrupt_cntxt_c            cntxt;

   // Components
   uvma_interrupt_mon_c              monitor;
   uvma_interrupt_drv_c              driver;
   uvma_interrupt_sqr_c              sequencer;
   uvma_interrupt_cov_model_c        cov_model;

   `uvm_component_utils_begin(uvma_interrupt_agent_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_agent", uvm_component parent=null);

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
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
   extern function void get_and_set_cfg();

   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern function void get_and_set_cntxt();

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
    * Connects coverage model to monitor and driver's analysis ports.
    */
   extern function void connect_cov_model();

endclass : uvma_interrupt_agent_c


function uvma_interrupt_agent_c::new(string name="uvma_interrupt_agent", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_interrupt_agent_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   get_and_set_cfg  ();
   get_and_set_cntxt();
   retrieve_vif     ();
   create_components();

endfunction : build_phase


function void uvma_interrupt_agent_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

   connect_sequencer_and_driver();
   connect_cov_model();

endfunction: connect_phase


function void uvma_interrupt_agent_c::get_and_set_cfg();

   void'(uvm_config_db#(uvma_interrupt_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_interrupt_cfg_c)::set(this, "*", "cfg", cfg);
   end

endfunction : get_and_set_cfg


function void uvma_interrupt_agent_c::get_and_set_cntxt();

   void'(uvm_config_db#(uvma_interrupt_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_info(get_type_name(), "Context handle is null; creating.", UVM_DEBUG)
      cntxt = uvma_interrupt_cntxt_c::type_id::create("cntxt");
   end
   uvm_config_db#(uvma_interrupt_cntxt_c)::set(this, "*", "cntxt", cntxt);

endfunction : get_and_set_cntxt


function void uvma_interrupt_agent_c::retrieve_vif();

   if (!uvm_config_db#(virtual uvma_interrupt_if)::get(this, "", "interrupt_vif", cntxt.interrupt_vif)) begin
      `uvm_fatal(get_type_name(), $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.interrupt_vif)))
   end
   else begin
      `uvm_info(get_type_name(), $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.interrupt_vif)), UVM_DEBUG)
   end

endfunction : retrieve_vif


function void uvma_interrupt_agent_c::create_components();

   monitor            = uvma_interrupt_mon_c            ::type_id::create("monitor"        , this);
   if (cfg.is_active == UVM_ACTIVE) begin
      sequencer       = uvma_interrupt_sqr_c            ::type_id::create("sequencer"      , this);
      driver          = uvma_interrupt_drv_c            ::type_id::create("driver"         , this);
   end
   if (cfg.cov_model_enabled) begin
      cov_model          = uvma_interrupt_cov_model_c      ::type_id::create("cov_model"        , this);
   end

endfunction : create_components


function void uvma_interrupt_agent_c::connect_sequencer_and_driver();

   if (cfg.is_active == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
   end

endfunction : connect_sequencer_and_driver


function void uvma_interrupt_agent_c::connect_cov_model();

   if (cfg.cov_model_enabled) begin
      monitor.ap.connect(cov_model.seq_item_fifo.analysis_export);
   end

endfunction : connect_cov_model


`endif // __UVMA_INTERRUPT_AGENT_SV__
