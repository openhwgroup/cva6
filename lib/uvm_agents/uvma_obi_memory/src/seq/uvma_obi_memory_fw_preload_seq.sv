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


`ifndef __UVMA_OBI_MEMORY_FW_PRELOAD_SEQ_SV__
`define __UVMA_OBI_MEMORY_FW_PRELOAD_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvma_obi_memory_fw_preload_seq_c extends uvma_obi_memory_base_seq_c;

   string fw_file_path;

   `uvm_object_utils_begin(uvma_obi_memory_fw_preload_seq_c)
   `uvm_object_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_fw_preload_seq");
   
   /**
    * Implement the sequence using plusarg to load a firmware file
    */
   extern virtual task body();
   
endclass : uvma_obi_memory_fw_preload_seq_c

function uvma_obi_memory_fw_preload_seq_c::new(string name="uvma_obi_memory_fw_preload_seq");
   
   super.new(name);
   
endfunction : new

task uvma_obi_memory_fw_preload_seq_c::body();

   if ($value$plusargs("firmware=%s", fw_file_path)) begin
      cntxt.mem.readmemh(fw_file_path);
   end
   
endtask : body

`endif // __UVMA_OBI_MEMORY_FW_PRELOAD_SEQ_SV__
