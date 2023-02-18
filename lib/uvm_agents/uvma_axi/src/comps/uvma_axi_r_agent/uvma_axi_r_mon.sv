// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 monitor for  R channel ****/

`ifndef __UVMA_AXI_R_MON_SV__
`define __UVMA_AXI_R_MON_SV__

class uvma_axi_r_mon_c extends uvm_monitor;

   `uvm_component_utils(uvma_axi_r_mon_c)

   uvma_axi_cfg_c                         cfg;
   uvma_axi_cntxt_c                       cntxt;

   uvma_axi_r_item_c                      r_item;
   uvma_axi_r_item_c                      rdrv_item;
   uvma_axi_base_seq_item_c               transaction;

   uvm_analysis_port #(uvma_axi_r_item_c) uvma_r_mon_port;
   uvm_analysis_port #(uvma_axi_r_item_c) uvma_r_mon2drv_port;
   uvm_analysis_port#(uvma_axi_base_seq_item_c) r_mon2log_port;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.passive  passive_mp;
   virtual uvma_axi_intf  vif;

   extern function new(string name = "uvma_axi_r_mon_c", uvm_component parent);
   extern virtual function void build_phase(uvm_phase phase);
   extern virtual task run_phase(uvm_phase phase);
   extern task monitor_r_items();
   extern task observe_reset();

endclass:uvma_axi_r_mon_c

function uvma_axi_r_mon_c::new(string name = "uvma_axi_r_mon_c", uvm_component parent);

   super.new(name, parent);
   uvma_r_mon_port = new("uvma_r_mon_port", this);
   uvma_r_mon2drv_port = new("uvma_r_mon2drv_port", this);
   r_mon2log_port = new("r_mon2log_port", this);

endfunction

function void uvma_axi_r_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);
   void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

   void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end

   passive_mp = cntxt.axi_vi.passive;
   vif = cntxt.axi_vi;

   this.r_item = uvma_axi_r_item_c::type_id::create("r_item", this);
   this.rdrv_item = uvma_axi_r_item_c::type_id::create("rdrv_item", this);
   this.transaction = uvma_axi_base_seq_item_c::type_id::create("transaction", this);

endfunction

task uvma_axi_r_mon_c::run_phase(uvm_phase phase);

   super.run_phase(phase);
   fork
      this.observe_reset();
      this.monitor_r_items();
   join_none

endtask: run_phase

task uvma_axi_r_mon_c::monitor_r_items();
   forever begin

      // collect R signals
      `uvm_info(get_type_name(), $sformatf("read data, collect resp signals from interface"), UVM_HIGH)
      this.r_item.r_id    = passive_mp.psv_axi_cb.r_id;
      this.r_item.r_data  = passive_mp.psv_axi_cb.r_data;
      this.r_item.r_resp  = passive_mp.psv_axi_cb.r_resp;
      this.r_item.r_last  = passive_mp.psv_axi_cb.r_last;
      this.r_item.r_user  = passive_mp.psv_axi_cb.r_user;
      this.r_item.r_valid = passive_mp.psv_axi_cb.r_valid;
      this.r_item.r_ready = passive_mp.psv_axi_cb.r_ready;

      this.uvma_r_mon_port.write(r_item);

      if(cfg.is_active) begin
         // collect AR signals
         this.rdrv_item.r_id    = vif.r_id;
         this.rdrv_item.r_data  = vif.r_data;
         this.rdrv_item.r_resp  = vif.r_resp;
         this.rdrv_item.r_last  = vif.r_last;
         this.rdrv_item.r_user  = vif.r_user;
         this.rdrv_item.r_valid = vif.r_valid;
         this.rdrv_item.r_ready = vif.r_ready;
         this.uvma_r_mon2drv_port.write(this.rdrv_item);
      end

      this.transaction.r_id    = passive_mp.psv_axi_cb.r_id;
      this.transaction.r_data  = passive_mp.psv_axi_cb.r_data;
      this.transaction.r_valid = passive_mp.psv_axi_cb.r_valid;
      this.transaction.r_ready = passive_mp.psv_axi_cb.r_ready;
      this.transaction.r_resp  = passive_mp.psv_axi_cb.r_resp;
      this.transaction.r_last  = passive_mp.psv_axi_cb.r_last;
      if( cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
         this.r_mon2log_port.write(transaction);
      end

      @(passive_mp.psv_axi_cb);

   end

endtask:  monitor_r_items

task uvma_axi_r_mon_c::observe_reset();

   forever begin

      wait (cntxt.axi_vi.rst_n === 0);
      cntxt.reset_state = UVMA_AXI_RESET_STATE_IN_RESET;
      `uvm_info(get_type_name(), $sformatf("RESET_STATE_IN_RESET"), UVM_LOW)
      wait (cntxt.axi_vi.rst_n === 1);
      cntxt.reset_state = UVMA_AXI_RESET_STATE_POST_RESET;
      `uvm_info(get_type_name(), $sformatf("RESET_STATE_POST_RESET"), UVM_LOW)
   end

endtask : observe_reset

`endif
