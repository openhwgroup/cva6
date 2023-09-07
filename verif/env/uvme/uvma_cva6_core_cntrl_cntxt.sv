// Copyright 2023 OpenHW Group
// Copyright 2023 Datum Technology Corporation
// Copyright 2023 Silicon Labs, Inc.
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


`ifndef __UVMA_CVA6_CORE_CNTRL_CNTXT_SV__
`define __UVMA_CVA6_CORE_CNTRL_CNTXT_SV__


/**
 * Object encapsulating all state variables for all Rvvi agent
 * (uvma_core_cntrl_agent_c) components.
 */
 class uvma_cva6_core_cntrl_cntxt_c extends uvma_core_cntrl_cntxt_c;

   virtual uvme_cva6_core_cntrl_if core_cntrl_vif;

   `uvm_object_utils_begin(uvma_cva6_core_cntrl_cntxt_c)
   `uvm_object_utils_end

   /**
    * Builds events.
    */
   extern function new(string name="uvma_cva6_core_cntrl_cntxt");

endclass : uvma_cva6_core_cntrl_cntxt_c

`pragma protect begin

function uvma_cva6_core_cntrl_cntxt_c::new(string name="uvma_cva6_core_cntrl_cntxt");

   super.new(name);

endfunction : new

`pragma protect end


`endif // __UVMA_CVA6_CORE_CNTRL_CNTXT_SV__
