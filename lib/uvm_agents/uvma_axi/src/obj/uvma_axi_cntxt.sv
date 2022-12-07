// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

`ifndef __UVMA_AXI_CNTXT_SV__
`define __UVMA_AXI_CNTXT_SV__

/**
 * Object encapsulating all state variables for all AXI agent
 * (uvma_axi_agent_c) components.
 */
class uvma_axi_cntxt_c extends uvm_object;

   // Handle to agent interface
   virtual uvma_axi_intf  axi_vi;

   // Handle to memory storage for active slaves
   uvml_mem_c mem;

   uvma_axi_reset_state_enum  reset_state = UVMA_AXI_RESET_STATE_PRE_RESET;

   `uvm_object_utils_begin(uvma_axi_cntxt_c)
      `uvm_field_enum(uvma_axi_reset_state_enum, reset_state, UVM_DEFAULT)
   `uvm_object_utils_end
   /**
    * Builds events.
    */
   extern function new(string name = "uvma_axi_cntxt");

endclass : uvma_axi_cntxt_c


function uvma_axi_cntxt_c::new(string name = "uvma_axi_cntxt");

   super.new(name);
   mem = uvml_mem_c#(64)::type_id::create("mem");

endfunction : new

`endif // __UVMA_AXI_CNTXT_SV__
