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

   uvma_axi_cntxt_c                        cntxt;

   uvma_axi_b_item_c                       b_item;

   uvm_analysis_port #(uvma_axi_b_item_c)  uvma_b_mon_port;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.passive  passive_mp;

   extern function new(string name = "uvma_axi_b_mon_c", uvm_component parent);
   extern virtual function void build_phase(uvm_phase phase);
   extern virtual task run_phase(uvm_phase phase);
   extern task monitor_b_items();
endclass:uvma_axi_b_mon_c

function uvma_axi_b_mon_c::new(string name = "uvma_axi_b_mon_c", uvm_component parent);
   super.new(name, parent);
   this.uvma_b_mon_port     = new("uvma_b_mon_port", this);
endfunction

function void uvma_axi_b_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

   passive_mp = cntxt.axi_vi.passive;

   this.b_item = uvma_axi_b_item_c::type_id::create("b_item", this);

endfunction:build_phase

task uvma_axi_b_mon_c::run_phase(uvm_phase phase);
   super.run_phase(phase);
   this.monitor_b_items();
endtask: run_phase

task uvma_axi_b_mon_c::monitor_b_items();

   forever begin

      // collect b signals
      `uvm_info(get_type_name(), $sformatf("response, collect resp signals from interface"), UVM_LOW)
      this.b_item.b_id    = passive_mp.psv_axi_cb.b_id;
      this.b_item.b_resp  = passive_mp.psv_axi_cb.b_resp;
      this.b_item.b_user  = passive_mp.psv_axi_cb.b_user;
      this.b_item.b_valid = passive_mp.psv_axi_cb.b_valid;
      this.b_item.b_ready = passive_mp.psv_axi_cb.b_ready;
      this.uvma_b_mon_port.write(b_item);
      @(passive_mp.psv_axi_cb);

   end

endtask:  monitor_b_items

`endif
