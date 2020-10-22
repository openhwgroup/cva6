// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


`ifndef __UVMA_DEBUG_SEQ_ITEM_SV__
`define __UVMA_DEBUG_SEQ_ITEM_SV__


/**
 * Object created by Debug agent sequences extending uvma_debug_seq_base_c.
 */
class uvma_debug_seq_item_c extends uvml_trn_seq_item_c;
   
  bit debug_req; 
  rand int unsigned active_cycles;
   
   `uvm_object_utils_begin(uvma_debug_seq_item_c)
    `uvm_field_int(debug_req, UVM_DEFAULT)
    `uvm_field_int(active_cycles, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   // TODO Add uvma_debug_seq_item_c constraints
   //      Ex: constraint default_cons {
   //             abc inside {0,2,4,8,16,32};
   //          }
   constraint active_cons {
       active_cycles > 0 && active_cycles < 100;
   }
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_debug_seq_item");
   
endclass : uvma_debug_seq_item_c


`pragma protect begin


function uvma_debug_seq_item_c::new(string name="uvma_debug_seq_item");
   
   super.new(name);
   
endfunction : new


`pragma protect end


`endif // __UVMA_DEBUG_SEQ_ITEM_SV__
