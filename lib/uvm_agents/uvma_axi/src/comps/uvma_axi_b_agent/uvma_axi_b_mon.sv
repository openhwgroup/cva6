// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 B channel monitor  ****/

`ifndef __UVMA_AXI_B_MON_SV__
`define __UVMA_AXI_B_MON_SV__

class uvma_axi_b_mon_c extends uvm_monitor;

   `uvm_component_utils(uvma_axi_b_mon_c)

   uvma_axi_cfg_c                          cfg;
   uvma_axi_cntxt_c                        cntxt;

   uvma_axi_b_item_c                       b_item;
   uvma_axi_b_item_c                       bdrv_item;
   uvma_axi_base_seq_item_c                transaction;

   uvm_analysis_port #(uvma_axi_b_item_c)  uvma_b_mon_port;
   uvm_analysis_port #(uvma_axi_b_item_c)  uvma_b_mon2drv_port;
   uvm_analysis_port#(uvma_axi_base_seq_item_c) b_mon2log_port;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.passive  passive_mp;
   virtual uvma_axi_intf  vif;

   extern function new(string name = "uvma_axi_b_mon_c", uvm_component parent);
   extern virtual function void build_phase(uvm_phase phase);
   extern virtual task run_phase(uvm_phase phase);
   extern task monitor_b_items();
endclass:uvma_axi_b_mon_c

function uvma_axi_b_mon_c::new(string name = "uvma_axi_b_mon_c", uvm_component parent);
   super.new(name, parent);
   this.uvma_b_mon_port     = new("uvma_b_mon_port", this);
   this.uvma_b_mon2drv_port = new("uvma_b_mon2drv_port", this);
   this.b_mon2log_port = new("b_mon2log_port", this);
endfunction

function void uvma_axi_b_mon_c::build_phase(uvm_phase phase);

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

   this.b_item = uvma_axi_b_item_c::type_id::create("b_item", this);
   this.bdrv_item = uvma_axi_b_item_c::type_id::create("bdrv_item", this);
   this.transaction = uvma_axi_base_seq_item_c::type_id::create("transaction", this);

endfunction:build_phase

task uvma_axi_b_mon_c::run_phase(uvm_phase phase);
   super.run_phase(phase);
   this.monitor_b_items();
endtask: run_phase

task uvma_axi_b_mon_c::monitor_b_items();

   forever begin

      // collect b signals
      `uvm_info(get_type_name(), $sformatf("response, collect resp signals from interface"), UVM_HIGH)
      this.b_item.b_id    = passive_mp.psv_axi_cb.b_id;
      this.b_item.b_resp  = passive_mp.psv_axi_cb.b_resp;
      this.b_item.b_user  = passive_mp.psv_axi_cb.b_user;
      this.b_item.b_valid = passive_mp.psv_axi_cb.b_valid;
      this.b_item.b_ready = passive_mp.psv_axi_cb.b_ready;
      this.uvma_b_mon_port.write(b_item);

      if(cfg.is_active) begin
         // collect b signals
         this.bdrv_item.b_id    = vif.b_id;
         this.bdrv_item.b_resp  = vif.b_resp;
         this.bdrv_item.b_user  = vif.b_user;
         this.bdrv_item.b_valid = vif.b_valid;
         this.bdrv_item.b_ready = vif.b_ready;
         this.uvma_b_mon2drv_port.write(this.bdrv_item);
      end

      this.transaction.b_id    = passive_mp.psv_axi_cb.b_id;
      this.transaction.b_resp  = passive_mp.psv_axi_cb.b_resp;
      this.transaction.b_valid = passive_mp.psv_axi_cb.b_valid;
      this.transaction.b_ready = passive_mp.psv_axi_cb.b_ready;
      if( cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
         this.b_mon2log_port.write(transaction);
      end

      @(passive_mp.psv_axi_cb);

   end

endtask:  monitor_b_items

`endif
