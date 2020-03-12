// 
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
// 


`ifndef __UVMA_CLKNRST_SEQ_ITEM_SV__
`define __UVMA_CLKNRST_SEQ_ITEM_SV__


/**
 * Object created by Clock & Reset agent sequences extending
 * uvma_clknrst_seq_base_c.
 */
class uvma_clknrst_seq_item_c extends uvml_trn_seq_item_c;
   
   rand uvma_clknrst_seq_item_action_enum         action         ; ///< What operation to perform
   rand uvma_clknrst_seq_item_initial_value_enum  initial_value  ; ///< The initial value (if starting or asserting)
   
   rand int unsigned  clk_period         ; ///< Setting to 0 will conserve the current clock period
   rand int unsigned  rst_deassert_period; ///< The amount of time (ps) after which to deassert reset
   
   
   `uvm_object_utils_begin(uvma_clknrst_seq_item_c)
      `uvm_field_enum(uvma_clknrst_seq_item_action_enum       , action         , UVM_DEFAULT)
      `uvm_field_enum(uvma_clknrst_seq_item_initial_value_enum, initial_value  , UVM_DEFAULT)
      
      `uvm_field_int(clk_period         , UVM_DEFAULT)
      `uvm_field_int(rst_deassert_period, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   constraint default_cons {
      soft clk_period          == 0;
      soft rst_deassert_period == uvma_clknrst_default_rst_deassert_period;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_clknrst_seq_item");
   
endclass : uvma_clknrst_seq_item_c


function uvma_clknrst_seq_item_c::new(string name="uvma_clknrst_seq_item");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_CLKNRST_SEQ_ITEM_SV__
