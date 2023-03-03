// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 slave AW driver  ****/

`ifndef __UVMA_AXI_AW_DRV_SV__
`define __UVMA_AXI_AW_DRV_SV__

class uvma_axi_aw_drv_c extends uvm_driver #(uvma_axi_aw_item_c);

   `uvm_component_utils(uvma_axi_aw_drv_c)

   uvma_axi_cfg_c          cfg;
   uvma_axi_cntxt_c        cntxt;

   uvma_axi_aw_item_c    aw_item;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.slave  slave_mp;

   extern function new(string name = "uvma_axi_aw_drv_c", uvm_component parent);
   extern virtual  function void build_phase(uvm_phase phase);
   extern virtual  task run_phase(uvm_phase phase);
   extern task     drv_pre_reset();
   extern task     drv_in_reset();
   extern task     drv_post_reset();

endclass: uvma_axi_aw_drv_c

function uvma_axi_aw_drv_c::new(string name = "uvma_axi_aw_drv_c", uvm_component parent);
   super.new(name, parent);
endfunction

function void uvma_axi_aw_drv_c::build_phase(uvm_phase phase);
   super.build_phase(phase);
   if(!uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt)) begin
      `uvm_fatal("build_phase", "driver reset cntxt class failed")
   end
   this.slave_mp = this.cntxt.axi_vi.slave;
   aw_item = uvma_axi_aw_item_c::type_id::create("aw_item", this);

   void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
endfunction

task uvma_axi_aw_drv_c::run_phase(uvm_phase phase);
   super.run_phase(phase);
   forever begin
      case (cntxt.reset_state)
         UVMA_AXI_RESET_STATE_PRE_RESET  : drv_pre_reset ();
         UVMA_AXI_RESET_STATE_IN_RESET   : drv_in_reset  ();
         UVMA_AXI_RESET_STATE_POST_RESET : drv_post_reset();

         default: `uvm_fatal("AXI_Aw_DRV", $sformatf("Invalid reset_state: %0d", cntxt.reset_state))
      endcase
   end
endtask: run_phase

task uvma_axi_aw_drv_c::drv_pre_reset();

   this.slave_mp.slv_axi_cb.aw_ready <= 0;
   @(slave_mp.slv_axi_cb);

endtask: drv_pre_reset

task uvma_axi_aw_drv_c::drv_in_reset();

   this.slave_mp.slv_axi_cb.aw_ready <= 0;
   @(slave_mp.slv_axi_cb);

endtask: drv_in_reset

task uvma_axi_aw_drv_c::drv_post_reset();

   `uvm_info(get_type_name(), $sformatf("write address driver start"), UVM_HIGH)
   seq_item_port.get_next_item(aw_item);

      this.slave_mp.slv_axi_cb.aw_ready <= 1'b0;

      if(aw_item.aw_valid) begin
         repeat (aw_item.aw_latency) begin
            @(slave_mp.slv_axi_cb);
         end
         this.slave_mp.slv_axi_cb.aw_ready <= 1'b1;
      end
      @(slave_mp.slv_axi_cb);

   seq_item_port.item_done();

endtask: drv_post_reset

`endif

