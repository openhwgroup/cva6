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
   rand bit [31:0]                            irq_mask; // Interrupts to apply action to
   rand int unsigned                          skew[32]; // Skew (in cycles) before applying individual interrupt actions per interrupt
   rand int unsigned                          repeat_count; // Number of times to apply action to interrupt

   rand int unsigned                          no_skew_wgt;
   rand int unsigned                          skew_wgt;

   rand int unsigned                          small_mask_wgt;
   rand int unsigned                          large_mask_wgt;

   `uvm_object_utils_begin(uvma_interrupt_seq_item_c)
      `uvm_field_enum(uvma_interrupt_seq_item_action_enum, action, UVM_DEFAULT)
      `uvm_field_int(irq_mask, UVM_DEFAULT)
      `uvm_field_sarray_int(skew, UVM_DEFAULT)
      `uvm_field_int(no_skew_wgt, UVM_DEFAULT)
      `uvm_field_int(skew_wgt, UVM_DEFAULT)
      `uvm_field_int(repeat_count, UVM_DEFAULT)
      `uvm_field_int(small_mask_wgt, UVM_DEFAULT)
      `uvm_field_int(large_mask_wgt, UVM_DEFAULT)
   `uvm_object_utils_end
   
   constraint small_mask_wgt_c {
      small_mask_wgt inside {[3:7]};
   }

   constraint large_mask_wgt_c {
      large_mask_wgt inside {[0:3]};      
   }

   constraint irq_mask_order_c {
      solve small_mask_wgt before irq_mask;
      solve large_mask_wgt before irq_mask;
   }

   constraint irq_mask_c {      
      $countones(irq_mask) dist { [1:4]  :/ small_mask_wgt,
                                  [1:31] :/ large_mask_wgt
                                };
   }

   constraint valid_repeat_count_c {
      repeat_count != 0;   
   }

   constraint default_repeat_count_c {
      soft repeat_count == 1;
   }

   constraint valid_skew_wgt {
      no_skew_wgt + skew_wgt != 0;
      skew_wgt == 1;
      no_skew_wgt == 0;
   }

   constraint default_skew_wgt_c {
      no_skew_wgt inside {[0:5]};
      skew_wgt inside {[0:3]};
   }

   constraint skew_wgt_order_c {
      foreach (skew[i]) {
         solve skew_wgt before skew[i];
         solve no_skew_wgt before skew[i];
      }
   }
   
   constraint default_skew_c {
      foreach (skew[i]) {
         skew[i] dist { 0      :/ no_skew_wgt,
                        [1:32] :/ skew_wgt};
      }
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
