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
   
   rand int unsigned                          irq_set_delay; // Delay after set individual interrupt
   rand int unsigned                          irq_clear_delay; // Delay after clear individual interrupt

   rand bit [15:0]                            interrupt_vector; //the vector interrupts for the core under test
   rand bit [15:0]                            interrupt_channel_mask; //the vector interrupts for the core under test

   `uvm_object_utils_begin(uvma_interrupt_seq_item_c)
      `uvm_field_int(irq_set_delay, UVM_DEFAULT)
      `uvm_field_int(irq_clear_delay, UVM_DEFAULT)
      `uvm_field_int(interrupt_vector, UVM_DEFAULT)
      `uvm_field_int(interrupt_channel_mask, UVM_DEFAULT)
   `uvm_object_utils_end


   constraint default_irq_delay_c {
        irq_set_delay inside {[300: 500]};
        irq_clear_delay inside {0, 25, 50};
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
