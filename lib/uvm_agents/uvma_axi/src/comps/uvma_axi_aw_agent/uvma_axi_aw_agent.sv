// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 agent for write address****/

`ifndef __UVMA_AXI_AW_AGENT_SV__
`define __UVMA_AXI_AW_AGENT_SV__

class uvma_axi_aw_agent_c extends uvm_agent;

   uvma_axi_aw_mon_c  monitor;

   `uvm_component_utils_begin(uvma_axi_aw_agent_c)
      `uvm_field_object(monitor, UVM_ALL_ON)
   `uvm_component_utils_end

   function new(string name = "uvma_axi_aw_agent_c", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);

      super.build_phase(phase);
      this.monitor = uvma_axi_aw_mon_c::type_id::create("monitor", this);

   endfunction

endclass

`endif
