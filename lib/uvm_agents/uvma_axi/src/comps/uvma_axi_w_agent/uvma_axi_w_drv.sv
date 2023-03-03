// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 slave W channel driver  ****/

`ifndef __UVMA_AXI_W_DRV_SV__
`define __UVMA_AXI_W_DRV_SV__

class uvma_axi_w_drv_c extends uvm_driver #(uvma_axi_w_item_c);

   `uvm_component_utils(uvma_axi_w_drv_c)

   uvma_axi_cfg_c        cfg;
   uvma_axi_cntxt_c      cntxt;

   uvma_axi_w_item_c    w_item;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.slave  slave_mp;

   extern function new(string name = "uvma_axi_w_drv_c", uvm_component parent);
   extern virtual function void build_phase(uvm_phase phase);
   extern virtual task run_phase(uvm_phase phase);
   extern task     drv_pre_reset();
   extern task     drv_in_reset();
   extern task     drv_post_reset();

endclass:uvma_axi_w_drv_c

function uvma_axi_w_drv_c::new(string name = "uvma_axi_w_drv_c", uvm_component parent);
   super.new(name, parent);
endfunction

function void uvma_axi_w_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   if(!uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt)) begin
      `uvm_fatal("build_phase", "w_driver cntxt class failed")
   end

   this.slave_mp = this.cntxt.axi_vi.slave;

   w_item = uvma_axi_w_item_c::type_id::create("w_item", this);

   // get cfg handle  to driver
   void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

endfunction

task uvma_axi_w_drv_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   forever begin

      case (cntxt.reset_state)
         UVMA_AXI_RESET_STATE_PRE_RESET : drv_pre_reset ();
         UVMA_AXI_RESET_STATE_IN_RESET  : drv_in_reset  ();
         UVMA_AXI_RESET_STATE_POST_RESET : drv_post_reset();

         default: `uvm_fatal("AXI_w_DRV", $sformatf("Invalid reset_state: %0d", cntxt.reset_state))
      endcase

   end

endtask: run_phase

task uvma_axi_w_drv_c::drv_pre_reset();

   this.slave_mp.slv_axi_cb.w_ready <= 0;
   @(slave_mp.slv_axi_cb);

endtask: drv_pre_reset

task uvma_axi_w_drv_c::drv_in_reset();

   this.slave_mp.slv_axi_cb.w_ready <= 0;
   @(slave_mp.slv_axi_cb);

endtask: drv_in_reset

task uvma_axi_w_drv_c::drv_post_reset();

   seq_item_port.get_next_item(w_item);
      `uvm_info(get_type_name(), $sformatf("write data driver start"), UVM_HIGH)
      this.slave_mp.slv_axi_cb.w_ready <= w_item.w_ready;
      @(slave_mp.slv_axi_cb);
   seq_item_port.item_done();

endtask: drv_post_reset

`endif
