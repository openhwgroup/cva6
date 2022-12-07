// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 (top) agent ****/

`ifndef __UVMA_AXI_AGENT_SV__
`define __UVMA_AXI_AGENT_SV__

class uvma_axi_agent_c extends uvm_agent;

   `uvm_component_utils(uvma_axi_agent_c)

   uvma_axi_aw_agent_c        aw_agent;
   uvma_axi_w_agent_c         w_agent;
   uvma_axi_b_agent_c         b_agent;
   uvma_axi_ar_agent_c        ar_agent;
   uvma_axi_r_agent_c         r_agent;

   uvma_axi_cntxt_c    cntxt;

   function new(string name = "uvma_axi_agent_c", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);

      super.build_phase(phase);
      get_and_set_cntxt();
      retrieve_vif     ();
      create_components();

   endfunction : build_phase

   function void get_and_set_cntxt();

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_info("CNTXT", "Context handle is null; creating", UVM_DEBUG)
         cntxt = uvma_axi_cntxt_c::type_id::create("cntxt");
      end
      uvm_config_db#(uvma_axi_cntxt_c)::set(this, "*", "cntxt", cntxt);

   endfunction : get_and_set_cntxt

   function void retrieve_vif();

      if (!uvm_config_db#(virtual uvma_axi_intf)::get(this, "", "axi_vif", cntxt.axi_vi)) begin
         `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)))
      end
      else begin
         `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)), UVM_DEBUG)
      end

   endfunction : retrieve_vif

   function void create_components();

      this.aw_agent = uvma_axi_aw_agent_c :: type_id :: create("aw_agent", this);
      this.w_agent  = uvma_axi_w_agent_c  :: type_id :: create("w_agent",  this);
      this.b_agent  = uvma_axi_b_agent_c  :: type_id :: create("b_agent",  this);
      this.ar_agent = uvma_axi_ar_agent_c :: type_id :: create("ar_agent", this);
      this.r_agent  = uvma_axi_r_agent_c  :: type_id :: create("r_agent",  this);

   endfunction : create_components

endclass : uvma_axi_agent_c

`endif //__UVMA_AXI_AGENT_SV__
