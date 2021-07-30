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


`ifndef __UVMA_RVVI_CONTROL_SEQ_ITEM_SV__
`define __UVMA_RVVI_CONTROL_SEQ_ITEM_SV__


/**
 * Object created by Rvvi_control agent sequences extending uvma_rvvi_control_seq_base_c.
 */
class uvma_rvvi_control_seq_item_c#(int ILEN=DEFAULT_ILEN,
                                    int XLEN=DEFAULT_XLEN)  extends uvml_trn_seq_item_c;


   // Action to be taken (STEP, HALT, TRAP)
   rand uvma_rvvi_rm_action action;

   static protected string _log_format_string = "0x%08x %s 0x%01x 0x%08x";

   `uvm_object_param_utils_begin(uvma_rvvi_control_seq_item_c#(ILEN,XLEN))
      `uvm_field_enum(uvma_rvvi_rm_action, action, UVM_DEFAULT)
   `uvm_object_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_control_seq_item");

   /**
    * One-liner log message
    */
   extern function string convert2string();

endclass : uvma_rvvi_control_seq_item_c

`pragma protect begin


function uvma_rvvi_control_seq_item_c::new(string name="uvma_rvvi_control_seq_item");
   
   super.new(name);
   
endfunction : new

function string uvma_rvvi_control_seq_item_c::convert2string();
   return action.name();
endfunction : convert2string

`pragma protect end


`endif // __UVMA_RVVI_CONTROL_SEQ_ITEM_SV__
