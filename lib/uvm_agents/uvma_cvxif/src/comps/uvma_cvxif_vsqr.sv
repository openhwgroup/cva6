// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_VSQR_SV__
`define __UVMA_CVXIF_VSQR_SV__


/**
 * Component provides sequence items for uvma_cvxif_drv_c.
 */
class uvma_cvxif_vsqr_c extends uvm_sequencer#(uvma_cvxif_resp_item_c);

   // Analysis port to receive retirement events from monitor
   uvm_tlm_analysis_fifo #(uvma_cvxif_req_item_c) mm_req_fifo;

   // Objects
   uvma_cvxif_cfg_c    cfg;

   `uvm_component_utils_begin (uvma_cvxif_vsqr_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor.
   */
   extern function new(string name="uvma_cvxif_vsqr", uvm_component parent=null);

   extern virtual function void build_phase(uvm_phase phase);

endclass : uvma_cvxif_vsqr_c

function uvma_cvxif_vsqr_c::new(string name="uvma_cvxif_vsqr", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvma_cvxif_vsqr_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   mm_req_fifo = new("mm_req_fifo", this);

endfunction : build_phase


`endif // __UVMA_CVXIF_VSQR_SV__
