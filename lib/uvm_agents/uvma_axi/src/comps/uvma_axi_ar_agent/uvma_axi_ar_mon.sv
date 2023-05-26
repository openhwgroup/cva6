// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi


`ifndef __UVMA_AXI_AR_MON_SV__
`define __UVMA_AXI_AR_MON_SV__

class uvma_axi_ar_mon_c extends uvm_monitor;

   `uvm_component_utils(uvma_axi_ar_mon_c)

   uvma_axi_ar_item_c                           ar_item;
   uvma_axi_ar_item_c                           ardrv_item;
   uvma_axi_base_seq_item_c                     transaction;
   uvm_analysis_port#(uvma_axi_ar_item_c)       uvma_ar_mon_port;
   uvm_analysis_port#(uvma_axi_ar_item_c)       uvma_ar_mon2drv_port;
   uvm_analysis_port#(uvma_axi_base_seq_item_c) ar_mon2log_port;
   uvma_axi_cfg_c     cfg;
   uvma_axi_cntxt_c   cntxt;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.passive  passive_mp;
   virtual uvma_axi_intf  vif;

   function new(string name = "uvma_axi_ar_mon_c", uvm_component parent);
      super.new(name, parent);
      this.uvma_ar_mon_port = new("uvma_ar_mon_port", this);
      this.uvma_ar_mon2drv_port = new("uvma_ar_mon2drv_port", this);
      this.ar_mon2log_port = new("ar_mon2log_port", this);
   endfunction

   function void build_phase(uvm_phase phase);

      super.build_phase(phase);
      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

      passive_mp = cntxt.axi_vi.passive;
      vif = cntxt.axi_vi;

      ar_item = uvma_axi_ar_item_c::type_id::create("ar_item", this);
      ardrv_item = uvma_axi_ar_item_c::type_id::create("ardrv_item", this);
      transaction = uvma_axi_base_seq_item_c::type_id::create("transaction", this);

      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end

   endfunction

   task run_phase(uvm_phase phase);

      super.run_phase(phase);
      monitor_ar_items();

   endtask: run_phase

   //Process for request from AR channel
   task monitor_ar_items();

      forever begin
         if(this.passive_mp.psv_axi_cb.ar_valid) begin
            // collect AR signals
            `uvm_info(get_type_name(), $sformatf("read address, collect AR signals and send item"), UVM_HIGH)
            this.ar_item.ar_id    = passive_mp.psv_axi_cb.ar_id;
            this.ar_item.ar_addr  = passive_mp.psv_axi_cb.ar_addr;
            this.ar_item.ar_len   = passive_mp.psv_axi_cb.ar_len;
            this.ar_item.ar_size  = passive_mp.psv_axi_cb.ar_size;
            this.ar_item.ar_burst = passive_mp.psv_axi_cb.ar_burst;
            this.ar_item.ar_user  = passive_mp.psv_axi_cb.ar_user;
            this.ar_item.ar_valid = passive_mp.psv_axi_cb.ar_valid;
            this.ar_item.ar_ready = passive_mp.psv_axi_cb.ar_ready;
            this.ar_item.ar_lock  = passive_mp.psv_axi_cb.ar_lock;
         end  else begin
            if( cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
               this.ar_item.ar_id    = 0;
               this.ar_item.ar_addr  = 0;
               this.ar_item.ar_len   = 0;
               this.ar_item.ar_size  = 0;
               this.ar_item.ar_burst = 0;
               this.ar_item.ar_user  = 0;
               this.ar_item.ar_valid = 0;
               this.ar_item.ar_ready = 0;
               this.ar_item.ar_lock  = 0;
            end
         end
         if(cfg.is_active) begin
            // collect AR signals
            this.ardrv_item.ar_id    = vif.ar_id;
            this.ardrv_item.ar_addr  = vif.ar_addr;
            this.ardrv_item.ar_len   = vif.ar_len;
            this.ardrv_item.ar_size  = vif.ar_size;
            this.ardrv_item.ar_burst = vif.ar_burst;
            this.ardrv_item.ar_user  = vif.ar_user;
            this.ardrv_item.ar_valid = vif.ar_valid;
            this.ardrv_item.ar_ready = vif.ar_ready;
            this.ardrv_item.ar_lock  = vif.ar_lock;
            this.uvma_ar_mon2drv_port.write(this.ardrv_item);
         end
         this.uvma_ar_mon_port.write(this.ar_item);

         this.transaction.ar_id    = passive_mp.psv_axi_cb.ar_id;
         this.transaction.ar_addr  = passive_mp.psv_axi_cb.ar_addr;
         this.transaction.ar_valid = passive_mp.psv_axi_cb.ar_valid;
         this.transaction.ar_ready = passive_mp.psv_axi_cb.ar_ready;
         this.transaction.ar_lock  = passive_mp.psv_axi_cb.ar_lock;
         if( cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
             this.ar_mon2log_port.write(transaction);
         end

         @(passive_mp.psv_axi_cb); 
      end
   endtask:  monitor_ar_items

endclass

`endif
