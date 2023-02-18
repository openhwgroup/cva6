// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)

/**** AXI4 master sequencer  ****/

`ifndef __UVMA_AXI_AW_SQR_SV__
`define __UVMA_AXI_AW_SQR_SV__

class uvma_axi_aw_sqr_c extends uvm_sequencer#(uvma_axi_aw_item_c);

   `uvm_component_utils(uvma_axi_aw_sqr_c)

   // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   uvm_analysis_export   #(uvma_axi_aw_item_c)    aw_req_export;
   uvm_tlm_analysis_fifo #(uvma_axi_aw_item_c)    aw_req_fifo;

   function new(string name = "uvma_axi_aw_sqr_c", uvm_component parent = null);

      super.new(name, parent);

      this.aw_req_export = new("aw_req_export", this);
      this.aw_req_fifo   = new("aw_req_fifo", this);

      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("CNTXT", "Context handle is null")
      end

   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      this.aw_req_export.connect(this.aw_req_fifo.analysis_export);       // Connect analysis export direct to fifo aw channels
   endfunction

endclass

`endif
