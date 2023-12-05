// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_SEQ_ITEM_SV__
`define __UVMA_INTERRUPT_SEQ_ITEM_SV__


/**
 * Object created by Interrupt agent sequences extending uvma_interrupt_seq_base_c.
 */
class uvma_interrupt_seq_item_c extends uvml_trn_seq_item_c;
   
   rand uvma_interrupt_cntrl_enum             irq_cntrl;
   rand int unsigned                          irq_delay; // Delay before applying individual interrupt
   rand int unsigned                          irq_time; // How many cycles take an interrupt

   rand bit[NUM_IRQ-1:0]                      interrupt_valid; //the valid interrupts for the core under test

   `uvm_object_utils_begin(uvma_interrupt_seq_item_c)
      `uvm_field_enum(uvma_interrupt_cntrl_enum, irq_cntrl, UVM_DEFAULT)
      `uvm_field_int(irq_delay, UVM_DEFAULT)
      `uvm_field_int(irq_time, UVM_DEFAULT)
      `uvm_field_int(interrupt_valid, UVM_DEFAULT)
   `uvm_object_utils_end


   constraint default_irq_delay_c {
        irq_delay inside {[150:250]};
   }

   constraint default_irq_time_c {
        irq_time inside {[5:10]};
   }

   constraint irq_mode_c {

      if (irq_cntrl == UVMA_INTERRUPT_ONE_BY_ONE) {
        $countones(interrupt_valid) == 1;
      }
      if (irq_cntrl == UVMA_INTERRUPT_MORE_THAN_ONE) {
        $countones(interrupt_valid) > 1;
      }
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_seq_item");
   
endclass : uvma_interrupt_seq_item_c

function uvma_interrupt_seq_item_c::new(string name="uvma_interrupt_seq_item");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_INTERRUPT_SEQ_ITEM_SV__
