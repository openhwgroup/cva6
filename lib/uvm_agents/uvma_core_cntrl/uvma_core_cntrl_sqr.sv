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


`ifndef __UVMA_CORE_CNTRL_SQR_SV__
`define __UVMA_CORE_CNTRL_SQR_SV__

/**
 * Component running Clock & Reset sequences extending uvma_rvvi_seq_base_c.
 * Provides sequence items for uvma_rvvi_drv_c.
 */
class uvma_core_cntrl_sqr_c extends uvm_sequencer;

   // Objects
   uvma_core_cntrl_cfg_c    cfg;
   uvma_core_cntrl_cntxt_c  cntxt;

   `uvm_component_utils_begin(uvma_core_cntrl_sqr_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_core_cntrl_sqr", uvm_component parent=null);
   
   /**
    * Ensures cfg & cntxt handles are not null
    */
   extern virtual function void build_phase(uvm_phase phase);

endclass : uvma_core_cntrl_sqr_c


function uvma_core_cntrl_sqr_c::new(string name="uvma_core_cntrl_sqr", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_core_cntrl_sqr_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_core_cntrl_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_core_cntrl_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
endfunction : build_phase

`endif // __UVMA_CORE_CNTRL_SQR_SV__
