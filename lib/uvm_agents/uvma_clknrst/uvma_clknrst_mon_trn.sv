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


`ifndef __UVMA_CLKNRST_MON_TRN_SV__
`define __UVMA_CLKNRST_MON_TRN_SV__


/**
 * Object rebuilt from the Clock & Reset monitor. Analog of
 * uvma_clknrst_seq_item_c.
 */
class uvma_clknrst_mon_trn_c extends uvml_trn_mon_trn_c;
   
   // Metadata
   uvma_clknrst_mon_trn_event_enum  event_type;
   
   // Data
   realtime clk_period          = 0;
   realtime reset_pulse_length  = 0;
   
   
   `uvm_object_utils_begin(uvma_clknrst_mon_trn_c)
      `uvm_field_enum(uvma_clknrst_mon_trn_event_enum, event_type, UVM_DEFAULT)
      
      `uvm_field_real(clk_period        , UVM_DEFAULT)
      `uvm_field_real(reset_pulse_length, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_clknrst_mon_trn");
   
endclass : uvma_clknrst_mon_trn_c


function uvma_clknrst_mon_trn_c::new(string name="uvma_clknrst_mon_trn");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_CLKNRST_MON_TRN_SV__
