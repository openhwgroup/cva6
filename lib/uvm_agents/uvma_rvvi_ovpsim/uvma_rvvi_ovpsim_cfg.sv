// 
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
// 


`ifndef __UVMA_RVVI_OVPSIM_CFG_SV__
`define __UVMA_RVVI_OVPSIM_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Clock & Reset agent (uvma_rvvi_agent_c) components.
 */
class uvma_rvvi_ovpsim_cfg_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN,
                              int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN) extends uvma_rvvi_cfg_c#(ILEN,XLEN);

   `uvm_object_utils_begin(uvma_rvvi_ovpsim_cfg_c)
   `uvm_object_utils_end
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_ovpsim_cfg");   

endclass : uvma_rvvi_ovpsim_cfg_c

function uvma_rvvi_ovpsim_cfg_c::new(string name="uvma_rvvi_ovpsim_cfg");
   
   super.new(name);
   
endfunction : new

`endif // __UVMA_RVVI_OVPSIM_CFG_SV__
