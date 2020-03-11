// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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


`ifndef __UVML_TRN_MON_TRN_SV__
`define __UVML_TRN_MON_TRN_SV__


/**
 * TODO Describe uvml_trn_mon_trn_c
 */
class uvml_trn_mon_trn_c extends uvm_sequence_item;
   
   bit       may_drop  = 0;
   bit       has_error = 0;
   realtime  timestamp = $realtime();
   
   
   `uvm_object_utils_begin(uvml_trn_mon_trn_c)
      `uvm_field_int (may_drop , UVM_DEFAULT + UVM_NOPACK + UVM_NOCOMPARE)
      `uvm_field_int (has_error, UVM_DEFAULT + UVM_NOPACK + UVM_NOCOMPARE)
      `uvm_field_real(timestamp, UVM_DEFAULT + UVM_NOPACK + UVM_NOCOMPARE)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor
    */
   extern function new(string name="uvml_trn_mon_trn");
   
endclass : uvml_trn_mon_trn_c


function uvml_trn_mon_trn_c::new(string name="uvml_trn_mon_trn");
   
   super.new(name);
   
endfunction : new


`endif // __UVML_TRN_MON_TRN_SV__
