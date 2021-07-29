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

`ifndef __UVMA_OBI_MEMORY_VP_CYCLE_COUNTER_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_CYCLE_COUNTER_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvma_obi_memory_vp_cycle_counter_seq_c extends uvma_obi_memory_vp_base_seq_c;

   longint unsigned cycle_counter;

   protected bit _stop_count_cycles;

   `uvm_object_utils_begin(uvma_obi_memory_vp_cycle_counter_seq_c)
      `uvm_field_int(cycle_counter, UVM_DEFAULT)      
   `uvm_object_utils_end
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_cycle_counter_seq_c");

   /**
    * Body will start cycle counting thread before starting parent
    */
   extern virtual task body();

   /**
    * Implement sequence that will return a random number
    */
   extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Implements the counting thread, should always be fork-join_none'd
    */
   extern virtual task count_cycles();

endclass : uvma_obi_memory_vp_cycle_counter_seq_c

function uvma_obi_memory_vp_cycle_counter_seq_c::new(string name="uvma_obi_memory_vp_cycle_counter_seq_c");
   
   super.new(name);
   
endfunction : new


task uvma_obi_memory_vp_cycle_counter_seq_c::body();

   fork
      count_cycles();
   join_none

   super.body();

endtask : body

task uvma_obi_memory_vp_cycle_counter_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);
   
   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   `uvm_create(slv_rsp)
   
   slv_rsp.err = 1'b0;
   //slv_rsp.gnt_latency    = 1;
   slv_rsp.access_latency = 1;
   //slv_rsp.hold_duration  = 1;
   slv_rsp.tail_length    = 1;   

   if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      // First stop the thread, reset counter to write data, then restart
      
      _stop_count_cycles = 1;
      wait (_stop_count_cycles == 0);

      cycle_counter = mon_trn.data;
      fork         
         count_cycles();
      join_none
   end
   else if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin      
      slv_rsp.rdata = cycle_counter;
   end

   slv_rsp.set_sequencer(p_sequencer);
   `uvm_send(slv_rsp)

endtask : vp_body

task uvma_obi_memory_vp_cycle_counter_seq_c::count_cycles();

   fork begin
      fork
         begin
            wait  (_stop_count_cycles == 1);
         end
         begin
            while(1) begin
               @(cntxt.vif.mon_cb);
               cycle_counter++;
            end
         end
      join_any

      // kill counting thread
      disable fork;

      // Handshake that the thread is stopped
      _stop_count_cycles = 0;
   end
   join

endtask : count_cycles

`endif // __UVMA_OBI_MEMORY_VP_CYCLE_COUNTER_SEQ_SV__
