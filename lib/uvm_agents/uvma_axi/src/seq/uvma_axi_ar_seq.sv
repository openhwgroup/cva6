// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)

//=============================================================================
// Description: Sequence for agent axi_ar
//=============================================================================

`ifndef UVMA_AXI_AR_SEQ_SV
`define UVMA_AXI_AR_SEQ_SV

class uvma_axi_ar_seq_c extends uvm_sequence#(uvma_axi_ar_item_c);

   `uvm_object_utils(uvma_axi_ar_seq_c)
   `uvm_declare_p_sequencer(uvma_axi_ar_sqr_c)

   // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;
   uvma_axi_ar_item_c  req_item;

   extern function new(string name = "");
   extern function void add_latencies(uvma_axi_ar_item_c master_req);
   extern task body();

endclass : uvma_axi_ar_seq_c


function uvma_axi_ar_seq_c::new(string name = "");
   super.new(name);
endfunction : new

function void uvma_axi_ar_seq_c::add_latencies(uvma_axi_ar_item_c master_req);

   master_req.ar_latency = cfg.calc_random_latency();

endfunction : add_latencies

task uvma_axi_ar_seq_c::body();
   forever begin
      cfg   = p_sequencer.cfg;
      cntxt = p_sequencer.cntxt;

      req_item = uvma_axi_ar_item_c::type_id::create("req_item");
      p_sequencer.ar_req_fifo.get(req_item);

      start_item(req_item);
         `uvm_info(get_type_name(), "READ ADDRESS sequence starting", UVM_HIGH)
         add_latencies(req_item);
      finish_item(req_item);
   end
   `uvm_info(get_type_name(), "Default sequence completed", UVM_HIGH)

endtask : body

`endif

