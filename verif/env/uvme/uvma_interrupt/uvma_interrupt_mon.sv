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
   uvm_analysis_port #(uvma_interrupt_seq_item_c)         ap;

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
    * Monitors passive_mp for asynchronous reset and updates the context's reset state.
    */
   extern task observe_reset();

   /**
    * Monitor pre-reset phase
    */
   extern virtual task mon_irq_pre_reset();

   /**
    * Monitor in-reset phase
    */
   extern virtual task mon_irq_in_reset();

   /**
    * Monitor post-reset phase
    */
   extern virtual task mon_irq_post_reset();

   //~ /**
    //~ * Monitor interrupt
    //~ */
   //~ extern virtual task mon_irq();

endclass : uvma_interrupt_mon_c


function uvma_interrupt_mon_c::new(string name = "uvma_interrupt_mon", uvm_component parent);
   super.new(name, parent);

endfunction


function void uvma_interrupt_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_interrupt_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal(get_type_name(), "monitor cntxt class failed")
   end

   void'(uvm_config_db#(uvma_interrupt_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal(get_type_name(), "Configuration handle is null")
   end

   ap  = new("ap", this);

endfunction


task uvma_interrupt_mon_c::run_phase(uvm_phase phase);
   super.run_phase(phase);


   if (cfg.enabled) begin
      fork
         observe_reset();

         forever begin
            case (cntxt.reset_state)
               UVMA_INTERRUPT_RESET_STATE_PRE_RESET:  mon_irq_pre_reset();
               UVMA_INTERRUPT_RESET_STATE_IN_RESET:   mon_irq_in_reset();
               UVMA_INTERRUPT_RESET_STATE_POST_RESET: mon_irq_post_reset();
            endcase
         end
      join
   end

endtask: run_phase


task uvma_interrupt_mon_c::mon_irq_pre_reset();

   @(cntxt.interrupt_vif.clk);

endtask : mon_irq_pre_reset

task uvma_interrupt_mon_c::mon_irq_in_reset();

   @(cntxt.interrupt_vif.clk);

endtask : mon_irq_in_reset

task uvma_interrupt_mon_c::mon_irq_post_reset();

   uvma_interrupt_seq_item_c   irq_item;

   while(1) begin
      @(cntxt.interrupt_vif.irq);

      irq_item = uvma_interrupt_seq_item_c::type_id::create("irq_item");
      irq_item.interrupt_vector = cntxt.interrupt_vif.irq;
      `uvm_info(get_type_name(), $sformatf("monitor interrupt : %0d", irq_item.interrupt_vector), UVM_LOW)
      ap.write(irq_item);

   end

endtask: mon_irq_post_reset


task uvma_interrupt_mon_c::observe_reset();

   forever begin
      wait (cntxt.interrupt_vif.reset_n === 0);
      cntxt.reset_state = UVMA_INTERRUPT_RESET_STATE_IN_RESET;
      `uvm_info(get_type_name(), $sformatf("RESET_STATE_IN_RESET"), UVM_NONE)
      wait (cntxt.interrupt_vif.reset_n === 1);
      cntxt.reset_state = UVMA_INTERRUPT_RESET_STATE_POST_RESET;
      `uvm_info(get_type_name(), $sformatf("RESET_STATE_POST_RESET"), UVM_NONE)
   end

endtask : observe_reset

`endif
