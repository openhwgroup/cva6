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


`ifndef __UVMA_OBI_SEQ_ITEM_SV__
`define __UVMA_OBI_SEQ_ITEM_SV__


/**
 * Object created by Obi agent sequences extending uvma_obi_seq_base_c.
 */
class uvma_obi_seq_item_c extends uvml_trn_seq_item_c;

   rand bit [31:0]     addr;
   rand bit [31:0]     data;
   rand bit [3:0]      we;
   rand bit [3:0]      be;   

   static protected string _log_format_string = "0x%08x %s 0x%01x 0x%08x";

   `uvm_object_utils_begin(uvma_obi_seq_item_c)
      `uvm_field_int(addr, UVM_DEFAULT)
      `uvm_field_int(data, UVM_DEFAULT)
      `uvm_field_int(we, UVM_DEFAULT)
      `uvm_field_int(be, UVM_DEFAULT)
   `uvm_object_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_seq_item");

   /**
    * One-liner log message
    */
   extern function string convert2string();

endclass : uvma_obi_seq_item_c

`pragma protect begin


function uvma_obi_seq_item_c::new(string name="uvma_obi_seq_item");
   
   super.new(name);
   
endfunction : new

function string uvma_obi_seq_item_c::convert2string();
  convert2string = $sformatf(_log_format_string,                             
                             addr, 
                             we ? "WR" : "RD",
                             be,
                             data);
endfunction : convert2string


`pragma protect end


`endif // __UVMA_OBI_SEQ_ITEM_SV__
