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


`ifndef __UVMA_RVVI_OVPSIM_CNTXT_SV__
`define __UVMA_RVVI_OVPSIM_CNTXT_SV__


/**
 * Object encapsulating all state variables for all Rvvi agent
 * (uvma_rvvi_ovpsim_agent_c) components.
 */
class uvma_rvvi_ovpsim_cntxt_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN,
                                int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN) extends uvma_rvvi_cntxt_c#(ILEN,XLEN);

   virtual RVVI_bus                     ovpsim_bus_vif;
   virtual RVVI_io                      ovpsim_io_vif;
   virtual RVVI_memory                  ovpsim_mem_vif;

   `uvm_object_param_utils_begin(uvma_rvvi_ovpsim_cntxt_c)
   `uvm_object_utils_end

   /**
    * Builds events.
    */
   extern function new(string name="uvma_rvvi_ovpsim_cntxt");

   /**
    * TODO Describe uvma_rvvi_ovpsim_cntxt_c::reset()
    */
   extern function void reset();

endclass : uvma_rvvi_ovpsim_cntxt_c


`pragma protect begin

function uvma_rvvi_ovpsim_cntxt_c::new(string name="uvma_rvvi_ovpsim_cntxt");

   super.new(name);

endfunction : new

function void uvma_rvvi_ovpsim_cntxt_c::reset();

endfunction : reset


`pragma protect end


`endif // __UVMA_RVVI_OVPSIM_CNTXT_SV__
