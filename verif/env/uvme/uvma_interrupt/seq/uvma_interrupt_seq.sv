// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_SEQ_SV__
`define __UVMA_INTERRUPT_SEQ_SV__


/**
 * Abstract object from which all other Interrupt agent sequences must extend.
 * Subclasses must be run on Interrupt sequencer (uvma_interrupt_sqr_c) instance.
 */
class uvma_interrupt_seq_c extends uvma_interrupt_base_seq_c;

   `uvm_object_utils(uvma_interrupt_seq_c)
   `uvm_declare_p_sequencer(uvma_interrupt_sqr_c)

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_seq");

   extern virtual task body();

endclass : uvma_interrupt_seq_c

function uvma_interrupt_seq_c::new(string name="uvma_interrupt_seq");

   super.new(name);

endfunction : new

task uvma_interrupt_seq_c::body();

  forever begin
        req_item = uvma_interrupt_seq_item_c::type_id::create("req_item");

        start_item(req_item);
        assert(req_item.randomize() with {
           if(!cfg.enable_interrupt){
              req_item.interrupt_valid == 'h0;
            }
            else {
              req_item.irq_cntrl != UVMA_INTERRUPT_RANDOMIZE;
              }
        })
        cfg.calc_random_req_latency();

        finish_item(req_item);
   end

endtask : body

`endif // __UVMA_INTERRUPT_SEQ_SV__
