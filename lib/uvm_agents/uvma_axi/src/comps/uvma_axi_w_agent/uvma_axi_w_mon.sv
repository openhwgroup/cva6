// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 W channel monitor  ****/

`ifndef __UVMA_AXI_W_MON_SV__
`define __UVMA_AXI_W_MON_SV__

class uvma_axi_w_mon_c extends uvm_monitor;

   `uvm_component_utils(uvma_axi_w_mon_c)

   uvma_axi_cntxt_c   cntxt;

   uvma_axi_w_item_c                                w_item;

   uvm_analysis_port #(uvma_axi_w_item_c)           uvma_w_mon_port;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.passive  passive_mp;

   extern function new(string name = "uvma_axi_w_mon_c", uvm_component parent);
   extern virtual  function void build_phase(uvm_phase phase);
   extern virtual  task run_phase(uvm_phase phase);
   extern task     monitor_w_items();

endclass:uvma_axi_w_mon_c

function uvma_axi_w_mon_c::new(string name = "uvma_axi_w_mon_c", uvm_component parent);

   super.new(name, parent);
   uvma_w_mon_port = new("uvma_w_mon_port", this);

endfunction

function void uvma_axi_w_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

   passive_mp = cntxt.axi_vi.passive;

   w_item = uvma_axi_w_item_c::type_id::create("w_item", this);

endfunction

task uvma_axi_w_mon_c::run_phase(uvm_phase phase);
   super.run_phase(phase);
   monitor_w_items();
endtask: run_phase

// Process for request from W channel
task uvma_axi_w_mon_c::monitor_w_items();
   forever begin
      `uvm_info(get_type_name(), $sformatf("write data, monitor DUT response and send data"), UVM_HIGH)
      w_item.w_strb  = passive_mp.psv_axi_cb.w_strb;
      w_item.w_data  = passive_mp.psv_axi_cb.w_data;
      w_item.w_last  = passive_mp.psv_axi_cb.w_last;
      w_item.w_user  = passive_mp.psv_axi_cb.w_user;
      w_item.w_valid = passive_mp.psv_axi_cb.w_valid;
      w_item.w_ready = passive_mp.psv_axi_cb.w_ready;
      this.uvma_w_mon_port.write(this.w_item);
      @(passive_mp.psv_axi_cb);
   end

endtask:  monitor_w_items

`endif
