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
    * Derived classes must implement
    */
   pure virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

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

`endif // __UVMA_OBI_MEMORY_VP_BASE_SEQ_SV__
