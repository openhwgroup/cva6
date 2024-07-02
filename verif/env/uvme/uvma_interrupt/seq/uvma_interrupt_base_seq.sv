// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_BASE_SEQ_SV__
`define __UVMA_INTERRUPT_BASE_SEQ_SV__


/**
 * Abstract object from which all other Interrupt agent sequences must extend.
 * Subclasses must be run on Interrupt sequencer (uvma_interrupt_sqr_c) instance.
 */
class uvma_interrupt_base_seq_c extends uvm_sequence#(uvma_interrupt_seq_item_c);
   
   `uvm_object_utils(uvma_interrupt_base_seq_c)
   `uvm_declare_p_sequencer(uvma_interrupt_sqr_c)   
   
   // Objects
   uvma_interrupt_cfg_c    cfg;
   uvma_interrupt_cntxt_c  cntxt;

   uvma_interrupt_seq_item_c  req_item;

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_base_seq");

   /**
    * Assigns cfg and cntxt handles from p_sequencer.
    */
   extern virtual task pre_start();

endclass : uvma_interrupt_base_seq_c

function uvma_interrupt_base_seq_c::new(string name="uvma_interrupt_base_seq");
   
   super.new(name);
   
endfunction : new

task uvma_interrupt_base_seq_c::pre_start();

   cfg   = p_sequencer.cfg;
   cntxt = p_sequencer.cntxt;

endtask : pre_start

`endif // __UVMA_INTERRUPT_BASE_SEQ_SV__
