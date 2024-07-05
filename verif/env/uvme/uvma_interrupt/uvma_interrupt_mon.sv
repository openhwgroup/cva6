// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

`ifndef __UVMA_INTERRUPT_MON_SV__
`define __UVMA_INTERRUPT_MON_SV__

class uvma_interrupt_mon_c extends uvm_monitor;

   // Objects
   uvma_interrupt_cfg_c                                   cfg;
   uvma_interrupt_cntxt_c                                 cntxt;

   `uvm_component_utils_begin(uvma_interrupt_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   // TLM
   uvm_analysis_port #(uvma_interrupt_seq_item_c)       ap;

  /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_mon", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Oversees monitoring via monitor_clk() and monitor_reset() tasks in parallel
    * forks.
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Monitor interrupt
    */
   extern virtual task mon_irq();

endclass : uvma_interrupt_mon_c

   /**
    * Default constructor.
    */
   function uvma_interrupt_mon_c::new(string name = "uvma_interrupt_mon", uvm_component parent);
      super.new(name, parent);

   endfunction

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   function void uvma_interrupt_mon_c::build_phase(uvm_phase phase);

      super.build_phase(phase);

      void'(uvm_config_db#(uvma_interrupt_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

      void'(uvm_config_db#(uvma_interrupt_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end
      
      ap  = new("ap", this);

   endfunction

   /**
    * TODO Describe uvma_interrupt_mon_c::run_phase()
    */
   task uvma_interrupt_mon_c::run_phase(uvm_phase phase);
      super.run_phase(phase);

      fork
         begin
             mon_irq();
         end
      join_none

   endtask: run_phase

   /**
    * TODO Describe uvma_interrupt_mon_c::mon_post_reset()
    */
   task uvma_interrupt_mon_c::mon_irq();

      uvma_interrupt_seq_item_c                          irq_item;

      while(1) begin
         @(cntxt.interrupt_vif.irq);

         irq_item = uvma_interrupt_seq_item_c::type_id::create("irq_item");
         irq_item.interrupt_valid = cntxt.interrupt_vif.irq;
         `uvm_info(get_type_name(), $sformatf("monitor interrupt : %0d", irq_item.interrupt_valid), UVM_LOW)
         ap.write(irq_item);

      end

   endtask: mon_irq

`endif
