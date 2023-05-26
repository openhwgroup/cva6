// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 (top) agent ****/

`ifndef __UVMA_AXI_AGENT_SV__
`define __UVMA_AXI_AGENT_SV__

class uvma_axi_agent_c extends uvm_agent;

   `uvm_component_utils(uvma_axi_agent_c)

   uvma_axi_aw_agent_c        aw_agent;
   uvma_axi_w_agent_c         w_agent;
   uvma_axi_b_agent_c         b_agent;
   uvma_axi_ar_agent_c        ar_agent;
   uvma_axi_r_agent_c         r_agent;
   uvma_axi_vsqr_c            vsequencer;

   uvma_axi_seq_item_logger_c seq_item_logger;

   uvma_axi_cfg_c      cfg;
   uvma_axi_cntxt_c    cntxt;

   function new(string name = "uvma_axi_agent_c", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);

      super.build_phase(phase);
      get_and_set_cfg  ();
      get_and_set_cntxt();
      retrieve_vif     ();
      create_components();

   endfunction : build_phase

   function void get_and_set_cntxt();

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_info("CNTXT", "Context handle is null; creating", UVM_DEBUG)
         cntxt = uvma_axi_cntxt_c::type_id::create("cntxt");
      end
      uvm_config_db#(uvma_axi_cntxt_c)::set(this, "*", "cntxt", cntxt);

   endfunction : get_and_set_cntxt

   function void get_and_set_cfg();

      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end
      else begin
         `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
         uvm_config_db#(uvma_axi_cfg_c)::set(this, "*", "cfg", cfg);
      end

   endfunction : get_and_set_cfg

   function void retrieve_vif();

      if (!uvm_config_db#(virtual uvma_axi_intf)::get(this, "", "axi_vif", cntxt.axi_vi)) begin
         `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)))
      end
      else begin
         `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)), UVM_DEBUG)
      end

   endfunction : retrieve_vif

   function void create_components();

      this.aw_agent = uvma_axi_aw_agent_c :: type_id :: create("aw_agent", this);
      this.w_agent  = uvma_axi_w_agent_c  :: type_id :: create("w_agent",  this);
      this.b_agent  = uvma_axi_b_agent_c  :: type_id :: create("b_agent",  this);
      this.ar_agent = uvma_axi_ar_agent_c :: type_id :: create("ar_agent", this);
      this.r_agent  = uvma_axi_r_agent_c  :: type_id :: create("r_agent",  this);
      this.seq_item_logger = uvma_axi_seq_item_logger_c::type_id::create("seq_item_logger", this);
      if( cfg.is_active == UVM_ACTIVE) begin
         vsequencer = uvma_axi_vsqr_c::type_id::create("sequencer", this);
      end

   endfunction : create_components

   function void connect_phase(uvm_phase phase);

      //super.connect_phase(phase);
      if( cfg.is_active == UVM_ACTIVE) begin
         connect_mon_2_sqr();
         assemble_vsequencer();
      end else begin
         `uvm_info(get_type_name(), $sformatf("PASSIVE MODE"), UVM_LOW)
      end

      if (cfg.trn_log_enabled) begin
         connect_trn_loggers();
         `uvm_info(get_type_name(), $sformatf("Transaction Loger enable"), UVM_LOW)
      end

   endfunction

   function void connect_mon_2_sqr();

      this.aw_agent.monitor.uvma_aw_mon2drv_port.connect(aw_agent.sequencer.aw_req_export);

      this.w_agent.monitor.uvma_w_mon2drv_port.connect(w_agent.sequencer.w_req_export);

      this.aw_agent.monitor.uvma_aw_mon2drv_port.connect(w_agent.sequencer.aw_req_export.analysis_export);

      this.aw_agent.monitor.uvma_aw_mon_port.connect(b_agent.sequencer.aw_req_export.analysis_export);

      this.w_agent.monitor.uvma_w_mon_port.connect(b_agent.sequencer.w_req_export.analysis_export);

      this.b_agent.monitor.uvma_b_mon2drv_port.connect(b_agent.sequencer.b_resp_export);

      this.ar_agent.monitor.uvma_ar_mon2drv_port.connect(ar_agent.sequencer.ar_req_export);

      this.ar_agent.monitor.uvma_ar_mon_port.connect(r_agent.sequencer.ar_req_export.analysis_export);

      this.r_agent.monitor.uvma_r_mon_port.connect(r_agent.sequencer.r_resp_export);

   endfunction: connect_mon_2_sqr

   function void assemble_vsequencer();

      vsequencer.aw_sequencer  = aw_agent.sequencer;
      vsequencer.ar_sequencer  = ar_agent.sequencer;
      vsequencer.w_sequencer   = w_agent.sequencer;
      vsequencer.b_sequencer   = b_agent.sequencer;
      vsequencer.r_sequencer   = r_agent.sequencer;

   endfunction: assemble_vsequencer

   function void connect_trn_loggers();

      this.aw_agent.monitor.aw_mon2log_port.connect(seq_item_logger.analysis_export);
      this.w_agent.monitor.w_mon2log_port.connect(seq_item_logger.analysis_export);
      this.b_agent.monitor.b_mon2log_port.connect(seq_item_logger.analysis_export);
      this.ar_agent.monitor.ar_mon2log_port.connect(seq_item_logger.analysis_export);
      this.r_agent.monitor.r_mon2log_port.connect(seq_item_logger.analysis_export);

   endfunction : connect_trn_loggers

endclass : uvma_axi_agent_c

`endif //__UVMA_AXI_AGENT_SV__
