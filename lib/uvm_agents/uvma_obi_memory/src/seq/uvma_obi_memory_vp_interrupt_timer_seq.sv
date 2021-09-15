// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 

`ifndef __UVMA_OBI_MEMORY_VP_INTERRUPT_TIMER_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_INTERRUPT_TIMER_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
virtual class uvma_obi_memory_vp_interrupt_timer_seq_c extends uvma_obi_memory_vp_base_seq_c;

   bit[31:0]    interrupt_value;
   int unsigned interrupt_timer_value;
   event        interrupt_timer_start;   

   `uvm_field_utils_begin(uvma_obi_memory_vp_interrupt_timer_seq_c)
      `uvm_field_int(interrupt_value,       UVM_DEFAULT)
      `uvm_field_int(interrupt_timer_value, UVM_DEFAULT)
   `uvm_field_utils_end
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_interrupt_timer_seq_c");

   /**
    * Body will start cycle counting thread before starting parent
    */
   extern virtual task body();

   /**
    * Implement number of peripherals
    */
   extern virtual function int unsigned get_num_words();

   /**
    * Implement sequence that will return a random number
    */
   extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Implements the interrupt_timer thread
    */
   extern virtual task interrupt_timer();

   /**
    * Must be implemented in dervied class to actually assert interrupt signals
    */
   pure virtual task set_interrupt();

endclass : uvma_obi_memory_vp_interrupt_timer_seq_c

function uvma_obi_memory_vp_interrupt_timer_seq_c::new(string name="uvma_obi_memory_vp_interrupt_timer_seq_c");
   
   super.new(name);
   
endfunction : new


task uvma_obi_memory_vp_interrupt_timer_seq_c::body();

   fork
      interrupt_timer();
   join_none

   super.body();

endtask : body

function int unsigned uvma_obi_memory_vp_interrupt_timer_seq_c::get_num_words();

   return 2;
   
endfunction : get_num_words

task uvma_obi_memory_vp_interrupt_timer_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);
   
   uvma_obi_memory_slv_seq_item_c  slv_rsp;

   `uvm_create(slv_rsp)
   slv_rsp.orig_trn = mon_trn;   
   slv_rsp.err = 1'b0;

   if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin

      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'interrupt_timer_control':\n%s", mon_trn.sprint()), UVM_HIGH)
      if (get_vp_index(mon_trn) == 0) begin
         interrupt_value = mon_trn.data;
      end
      else if (get_vp_index(mon_trn) == 1) begin
         interrupt_timer_value = mon_trn.data;
         ->interrupt_timer_start;
      end
      else begin
         `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'interrupt_timer_control':\n%s", mon_trn.sprint()), UVM_HIGH)
      end      
   end
   else if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      slv_rsp.rdata = 0;
   end
   
   add_r_fields(mon_trn, slv_rsp);
   slv_rsp.set_sequencer(p_sequencer);
   `uvm_send(slv_rsp)

endtask : vp_body

task uvma_obi_memory_vp_interrupt_timer_seq_c::interrupt_timer();

   while(1) begin
      @interrupt_timer_start;
      `uvm_info("VP_VSEQ", "@interrupt_timer_start", UVM_HIGH)
      while (interrupt_timer_value > 0) begin
         @(cntxt.vif.mon_cb);
         interrupt_timer_value = interrupt_timer_value - 1;
      end

      `uvm_info("VP_VSEQ", $sformatf("Done waiting for interrupt_timer_value to be 0, setting interrupts to 0x%08x", interrupt_value), UVM_HIGH)
      set_interrupt();
   end

endtask : interrupt_timer

`endif // __UVMA_OBI_MEMORY_VP_INTERRUPT_TIMER_SEQ_SV__
