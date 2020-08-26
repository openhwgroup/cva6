// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_INTERRUPT_SEQ_ITEM_SV__
`define __UVMA_INTERRUPT_SEQ_ITEM_SV__


/**
 * Object created by Interrupt agent sequences extending uvma_interrupt_seq_base_c.
 */
class uvma_interrupt_seq_item_c extends uvml_trn_seq_item_c;
   
   rand uvma_interrupt_seq_item_action_enum   action;
   rand bit [31:0]                            irq_mask;
   rand int unsigned                          repeat_count;

   `uvm_object_utils_begin(uvma_interrupt_seq_item_c)
      `uvm_field_enum(uvma_interrupt_seq_item_action_enum, action, UVM_DEFAULT)
      `uvm_field_int(irq_mask, UVM_DEFAULT)
      `uvm_field_int(repeat_count, UVM_DEFAULT)
   `uvm_object_utils_end
   
   constraint valid_repeat_count {
      repeat_count != 0;   
   }

   constraint default_repeat_count {
      soft repeat_count == 1;
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_seq_item");
   
endclass : uvma_interrupt_seq_item_c

`pragma protect begin


function uvma_interrupt_seq_item_c::new(string name="uvma_interrupt_seq_item");
   
   super.new(name);
   
endfunction : new


`pragma protect end


`endif // __UVMA_INTERRUPT_SEQ_ITEM_SV__
