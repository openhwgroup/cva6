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


`ifndef __UVMA_OBI_MON_TRN_SV__
`define __UVMA_OBI_MON_TRN_SV__


/**
 * Object rebuilt from the Obi monitor Analog of uvma_obi_seq_item_c.
 */
class uvma_obi_mon_trn_c extends uvma_obi_seq_item_c;
   

   `uvm_object_utils_begin(uvma_obi_mon_trn_c)
   `uvm_object_utils_end
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mon_trn");
   
endclass : uvma_obi_mon_trn_c


`pragma protect begin


function uvma_obi_mon_trn_c::new(string name="uvma_obi_mon_trn");
   
   super.new(name);
   
endfunction : new


`pragma protect end


`endif // __UVMA_OBI_MON_TRN_SV__
