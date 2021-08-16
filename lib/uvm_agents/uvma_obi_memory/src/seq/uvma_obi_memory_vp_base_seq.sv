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

`ifndef __UVMA_OBI_MEMORY_VP_BASE_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_BASE_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
virtual class uvma_obi_memory_vp_base_seq_c extends uvma_obi_memory_slv_base_seq_c;

   uvma_obi_memory_mon_trn_c       mon_trn_q[$]; // Used to add transactions to execute (monitored requests)

   // Base address of this virtual peripheral, used to generated offset index for multi-register
   // virtual perhipeerals
   // Should be filled in during registration
   bit [31:0] start_address; 

   `uvm_field_utils_begin(uvma_obi_memory_vp_base_seq_c)
   `uvm_field_utils_end
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_base_seq_c");
   
   /**
    * Simple loop that is triggered externally when the main slave sequence detects an address range
    * claimed by this virtual peripheral
    */
   extern virtual task body();

   /**
    * Utility to get an index for virtual peripheral with multiple registers
    */
   extern virtual function int unsigned get_vp_index(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Derived classes must implement the operation of the virtual peripheral
    */
   pure virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Derived classes must implement accessor to return number of virtual peripheral registers
    */
   pure virtual function int unsigned get_num_words();

endclass : uvma_obi_memory_vp_base_seq_c


function uvma_obi_memory_vp_base_seq_c::new(string name="uvma_obi_memory_vp_base_seq_c");
   
   super.new(name);
   
endfunction : new


task uvma_obi_memory_vp_base_seq_c::body();

   forever begin
      wait (mon_trn_q.size());

      vp_body(mon_trn_q.pop_front());   
   end

endtask : body


function int unsigned uvma_obi_memory_vp_base_seq_c::get_vp_index(uvma_obi_memory_mon_trn_c mon_trn);

   int unsigned index;

   // Fatal error if the address in the incoming transaction is less than the configured base address
   if (mon_trn.address < start_address) begin
      `uvm_fatal("FATAL", $sformatf("%s: get_vp_index(), mon_trn.address 0x%08x is less than start address 0x%08x", 
                                    this.get_name(), 
                                    mon_trn.address,
                                    start_address));
   end                                   

   index = (mon_trn.address - start_address) >> 2;

   // Fatal if the index is greater than expected
   if (index >= get_num_words()) begin
      `uvm_fatal("FATAL", $sformatf("%s: get_vp_index(), mon_trn.address 0x%08x base address 0x%08x, should only have %0s vp registers", 
                                    this.get_name(), 
                                    mon_trn.address,
                                    start_address,
                                    get_num_words()));
   end

   return index;

endfunction : get_vp_index


`endif // __UVMA_OBI_MEMORY_VP_BASE_SEQ_SV__
