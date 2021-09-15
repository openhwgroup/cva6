// 
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


`ifndef __UVML_TRN_SEQ_ITEM_SV__
`define __UVML_TRN_SEQ_ITEM_SV__


/**
 * TODO Describe uvml_trn_seq_item_c
 */
class uvml_trn_seq_item_c extends uvm_sequence_item;
   
   int unsigned  __uid       = 0;
   bit           __may_drop  = 0;
   bit           __has_error = 0;
   
   static int unsigned  __last_uid = 0;
   
  `uvm_object_utils_begin(uvml_trn_seq_item_c)
      `uvm_field_int(__may_drop , UVM_DEFAULT + UVM_NOPACK + UVM_NOCOMPARE)
      `uvm_field_int(__has_error, UVM_DEFAULT + UVM_NOPACK + UVM_NOCOMPARE)
  `uvm_object_utils_end
  
  
  /**
   * Default constructor
   */
  extern function new(string name="uvml_trn_seq_item");
  
endclass : uvml_trn_seq_item_c


function uvml_trn_seq_item_c::new(string name="uvml_trn_seq_item");
   
   super.new(name);
   __uid = __last_uid++;
  
endfunction : new


`endif // __UVML_TRN_SEQ_ITEM_SV__
