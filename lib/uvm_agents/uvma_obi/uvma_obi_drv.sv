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

`ifndef __UVMA_OBI_DRV_SV__
`define __UVMA_OBI_DRV_SV__

/**
 * Component driving a Clock & Reset virtual interface (uvma_obi_if).
 */
class uvma_obi_drv_c extends uvm_driver#(
   .REQ(uvma_obi_seq_item_c),
   .RSP(uvma_obi_seq_item_c)
);
   
   // Objects
   uvma_obi_cfg_c    cfg;
   uvma_obi_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_obi_seq_item_c)  ap;   
   
   `uvm_component_utils_begin(uvma_obi_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_drv", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * Obtains the reqs from the sequence item port and calls drv_req()
    */
   extern virtual task run_phase(uvm_phase phase);

endclass : uvma_obi_drv_c

function uvma_obi_drv_c::new(string name="uvma_obi_drv", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_drv_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_obi_cfg_c)::set(this, "*", "cfg", cfg);
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_obi_cntxt_c)::set(this, "*", "cntxt", cntxt);
   
   ap = new("ap", this);
   
endfunction : build_phase


task uvma_obi_drv_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);

   // Enable the driver in the interface
   cntxt.vif.is_active = 1;
   
endtask : run_phase


`endif // __UVMA_OBI_DRV_SV__
