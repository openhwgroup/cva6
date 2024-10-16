//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_SQR_SV__
`define __UVMA_INTERRUPT_SQR_SV__


/**
 * Component running interrupt sequences extending uvma_interrupt_seq_base_c.
 * Provides sequence items for uvma_interrupt_drv_c.
 */
class uvma_interrupt_sqr_c extends uvm_sequencer#(uvma_interrupt_seq_item_c);

   // Objects
   uvma_interrupt_cfg_c    cfg;
   uvma_interrupt_cntxt_c  cntxt;

   `uvm_component_utils_begin(uvma_interrupt_sqr_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_sqr", uvm_component parent=null);

   /**
    * Ensures cfg & cntxt handles are not null
    */
   extern virtual function void build_phase(uvm_phase phase);

endclass : uvma_interrupt_sqr_c


function uvma_interrupt_sqr_c::new(string name="uvma_interrupt_sqr", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_interrupt_sqr_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_interrupt_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal(get_type_name(), "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_interrupt_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal(get_type_name(), "Context handle is null")
   end

endfunction : build_phase


`endif // __UVMA_INTERRUPT_SQR_SV__
