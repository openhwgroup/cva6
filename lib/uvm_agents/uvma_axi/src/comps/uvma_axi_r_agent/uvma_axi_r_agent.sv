// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 agent for read ****/

`ifndef __UVMA_AXI_R_AGENT_SV__
`define __UVMA_AXI_R_AGENT_SV__

class uvma_axi_r_agent_c extends uvm_agent;

   uvma_axi_r_mon_c monitor;
   uvma_axi_r_sqr_c sequencer;
   uvma_axi_r_drv_c driver;
   uvma_axi_cfg_c   cfg;

   `uvm_component_utils_begin(uvma_axi_r_agent_c)
      `uvm_field_object(monitor, UVM_ALL_ON)
      `uvm_field_object(sequencer, UVM_ALL_ON)
      `uvm_field_object(driver, UVM_ALL_ON)
   `uvm_component_utils_end

   function new(string name = "uvma_axi_r_agent_c", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);

      super.build_phase(phase);

      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end

      if( cfg.is_active == UVM_ACTIVE) begin
         sequencer = uvma_axi_r_sqr_c::type_id::create("sequencer", this);
         driver    = uvma_axi_r_drv_c::type_id::create("driver", this);
      end
      monitor = uvma_axi_r_mon_c::type_id::create("monitor", this);

   endfunction

   function void connect_phase(uvm_phase phase);

      super.connect_phase(phase);
      //connect sequencer to driver
      if( cfg.is_active == UVM_ACTIVE) begin
         this.driver.seq_item_port.connect(this.sequencer.seq_item_export);
      end

   endfunction

endclass  : uvma_axi_r_agent_c

`endif
