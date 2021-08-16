// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
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


`ifndef __UVMA_OBI_MEMORY_MSTR_BASE_SEQ_SV__
`define __UVMA_OBI_MEMORY_MSTR_BASE_SEQ_SV__


/**
 * TODO Describe uvma_obi_memory_mstr_base_seq_c
 */
class uvma_obi_memory_mstr_base_seq_c extends uvma_obi_memory_base_seq_c;
   
   // Fields
   
   
   `uvm_object_utils_begin(uvma_obi_memory_mstr_base_seq_c)
      
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_mstr_base_seq");
   
   /**
    * TODO Describe uvma_obi_memory_mstr_base_seq_c::body()
    */
   extern virtual task body();
   
endclass : uvma_obi_memory_mstr_base_seq_c


function uvma_obi_memory_mstr_base_seq_c::new(string name="uvma_obi_memory_mstr_base_seq");
   
   super.new(name);
   
endfunction : new


task uvma_obi_memory_mstr_base_seq_c::body();
   
   // TODO Implement uvma_obi_memory_mstr_base_seq_c::body()
   
endtask : body


`endif // __UVMA_OBI_MEMORY_MSTR_BASE_SEQ_SV__
