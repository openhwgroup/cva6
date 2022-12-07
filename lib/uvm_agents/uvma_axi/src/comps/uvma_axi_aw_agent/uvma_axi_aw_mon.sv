// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi


`ifndef __UVMA_AXI_AW_MON_SV__
`define __UVMA_AXI_AW_MON_SV__

class uvma_axi_aw_mon_c extends uvm_monitor;

   `uvm_component_utils(uvma_axi_aw_mon_c)

   uvma_axi_cntxt_c   cntxt;

   uvma_axi_aw_item_c                      aw_item;

   uvm_analysis_port #(uvma_axi_aw_item_c) uvma_aw_mon_port;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.passive  passive_mp;

   function new(string name = "uvma_axi_aw_mon_c", uvm_component parent);
      super.new(name, parent);
      this.uvma_aw_mon_port = new("uvma_aw_mon_port", this);
   endfunction

   function void build_phase(uvm_phase phase);

      super.build_phase(phase);

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

      passive_mp = cntxt.axi_vi.passive;

      this.aw_item    = uvma_axi_aw_item_c::type_id::create("aw_item", this);

   endfunction

   task run_phase(uvm_phase phase);
      super.run_phase(phase);
      this.monitor_aw_items();
   endtask: run_phase

   // Process for request from AW channel
   task monitor_aw_items();

      forever begin
         if(passive_mp.psv_axi_cb.aw_valid) begin
            // collect AW signals
            `uvm_info(get_type_name(), $sformatf("write address, collect AW signals and send item"), UVM_HIGH)
            this.aw_item.aw_id    = passive_mp.psv_axi_cb.aw_id;
            this.aw_item.aw_addr  = passive_mp.psv_axi_cb.aw_addr;
            this.aw_item.aw_len   = passive_mp.psv_axi_cb.aw_len;
            this.aw_item.aw_size  = passive_mp.psv_axi_cb.aw_size;
            this.aw_item.aw_burst = passive_mp.psv_axi_cb.aw_burst;
            this.aw_item.aw_valid = passive_mp.psv_axi_cb.aw_valid;
            this.aw_item.aw_ready = passive_mp.psv_axi_cb.aw_ready;
            this.aw_item.aw_cache = passive_mp.psv_axi_cb.aw_cache;
            this.aw_item.aw_user  = passive_mp.psv_axi_cb.aw_user;
            this.aw_item.aw_lock  = passive_mp.psv_axi_cb.aw_lock;
            this.aw_item.aw_prot  = passive_mp.psv_axi_cb.aw_prot;
            this.aw_item.aw_qos   = passive_mp.psv_axi_cb.aw_qos;
            this.aw_item.aw_region= passive_mp.psv_axi_cb.aw_region;
            this.aw_item.aw_atop  = passive_mp.psv_axi_cb.aw_atop;
         end else begin
            if( cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
               this.aw_item.aw_id    = 0;
               this.aw_item.aw_addr  = 0;
               this.aw_item.aw_len   = 0;
               this.aw_item.aw_size  = 0;
               this.aw_item.aw_burst = 0;
               this.aw_item.aw_valid = 0;
               this.aw_item.aw_ready = 0;
               this.aw_item.aw_cache = 0;
               this.aw_item.aw_user  = 0;
               this.aw_item.aw_lock  = 0;
               this.aw_item.aw_prot  = 0;
               this.aw_item.aw_qos   = 0;
               this.aw_item.aw_region= 0;
               this.aw_item.aw_atop  = 0;
            end
         end
         this.uvma_aw_mon_port.write(this.aw_item);
         @(passive_mp.psv_axi_cb);
      end

   endtask:  monitor_aw_items

endclass

`endif
