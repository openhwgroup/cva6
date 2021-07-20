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


`ifndef __UVMA_CORE_CNTRL_CNTXT_SV__
`define __UVMA_CORE_CNTRL_CNTXT_SV__


/**
 * Object encapsulating all state variables for all core control
 * (uvma_core_cntrl_agent_c) components.
 */
virtual class uvma_core_cntrl_cntxt_c extends uvm_object;

   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;
   
   `uvm_field_utils_begin(uvma_core_cntrl_cntxt_c)
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_field_utils_end

   /**
    * Builds events.
    */
   extern function new(string name="uvma_core_cntrl_cntxt");
      
endclass : uvma_core_cntrl_cntxt_c


`pragma protect begin


function uvma_core_cntrl_cntxt_c::new(string name="uvma_core_cntrl_cntxt");
   
   super.new(name);
   
   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");
   
endfunction : new

`pragma protect end


`endif // __UVMA_CORE_CNTRL_CNTXT_SV__
