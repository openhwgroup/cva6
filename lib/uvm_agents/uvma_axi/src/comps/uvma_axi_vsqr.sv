// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 slave sequencer  ****/

`ifndef __UVMA_AXI_SQR_SV__
`define __UVMA_AXI_SQR_SV__

class uvma_axi_vsqr_c extends uvm_sequencer;

   `uvm_component_utils(uvma_axi_vsqr_c)

   // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   uvma_axi_aw_sqr_c         aw_sequencer;
   uvma_axi_ar_sqr_c         ar_sequencer;
   uvma_axi_w_sqr_c          w_sequencer;
   uvma_axi_b_sqr_c          b_sequencer;
   uvma_axi_r_sqr_c          r_sequencer;

   function new(string name = "uvma_axi_vsqr_c", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end
      
      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("CNTXT", "Context handle is null")
      end
   endfunction

endclass

`endif

