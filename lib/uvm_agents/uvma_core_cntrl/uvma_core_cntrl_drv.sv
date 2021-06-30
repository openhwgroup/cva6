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

`ifndef __UVMA_CORE_CNTRL_DRV_SV__
`define __UVMA_CORE_CNTRL_DRV_SV__

/**
 * Component driving a Clock & Reset virtual interface (uvma_core_cntrl_if).
 */
class uvma_core_cntrl_drv_c extends uvm_driver;

   // Objects
   uvma_core_cntrl_cfg_c    cfg;
   uvma_core_cntrl_cntxt_c  cntxt;   

   `uvm_component_utils_begin(uvma_core_cntrl_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_core_cntrl_drv", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Initialize signals
    */
   extern virtual task reset_phase(uvm_phase phase);

   /**
    * Obtains the reqs from the sequence item port and calls drv_req()
    */
   extern virtual task run_phase(uvm_phase phase);

   /** 
    * Drive bootstrap pins    
    */
   extern virtual task drive_bootstrap();

endclass : uvma_core_cntrl_drv_c

function uvma_core_cntrl_drv_c::new(string name="uvma_core_cntrl_drv", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new

function void uvma_core_cntrl_drv_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_core_cntrl_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "*", "cfg", cfg);
   
   void'(uvm_config_db#(uvma_core_cntrl_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_core_cntrl_cntxt_c)::set(this, "*", "cntxt", cntxt);
   
endfunction : build_phase

task uvma_core_cntrl_drv_c::reset_phase(uvm_phase phase);

   super.reset_phase(phase);

   drive_bootstrap();

endtask : reset_phase

task uvma_core_cntrl_drv_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
      
endtask : run_phase

task uvma_core_cntrl_drv_c::drive_bootstrap();
   
   `uvm_fatal("CORECNTRLDRV", "drive_bootstrap() must be overriden in any agent implementations");
      
endtask : drive_bootstrap

`endif // __UVMA_CORE_CNTRL_DRV_SV__
