// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_COV_MODEL_SV__
`define __UVMA_INTERRUPT_COV_MODEL_SV__

covergroup cg_interrupt(
    string name,
    int unsigned num_irq_supported
    ) with function
    sample(uvma_interrupt_seq_item_c req_item);

    option.per_instance = 1;
    option.name = name;

   cp_interrupt_req : coverpoint req_item.interrupt_vector {
      bins INTERRUPTS[] = {[0:$]} with (item inside {[0:(2**(num_irq_supported))-1]});
   }

endgroup: cg_interrupt

/**
 * Component encapsulating Interrupt functional coverage model.
 */
class uvma_interrupt_cov_model_c extends uvm_component;

   // Objects
   uvma_interrupt_cfg_c       cfg;
   uvma_interrupt_cntxt_c     cntxt;

   uvma_interrupt_seq_item_c  req_item;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_interrupt_seq_item_c)  seq_item_fifo;


   `uvm_component_utils_begin(uvma_interrupt_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   cg_interrupt          interrupt_cg;

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_cov_model", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);

endclass : uvma_interrupt_cov_model_c


function uvma_interrupt_cov_model_c::new(string name="uvma_interrupt_cov_model", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_interrupt_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_interrupt_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal(get_type_name(), "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_interrupt_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal(get_type_name(), "Context handle is null")
   end
   
   interrupt_cg = new("interrupt_cg",
                      .num_irq_supported(cfg.num_irq_supported));
   
   seq_item_fifo = new("seq_item_fifo", this);

endfunction : build_phase


task uvma_interrupt_cov_model_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   if (cfg.enabled && cfg.cov_model_enabled) begin

         // Sequence items
         forever begin
            seq_item_fifo.get(req_item);
            interrupt_cg.sample(req_item);
         end
   end

endtask : run_phase


`endif // __UVMA_INTERRUPT_COV_MODEL_SV__
