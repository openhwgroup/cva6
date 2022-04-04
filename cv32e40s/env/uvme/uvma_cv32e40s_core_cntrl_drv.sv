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

`ifndef __UVMA_CV32E40S_CORE_CNTRL_DRV_SV__
`define __UVMA_CV32E40S_CORE_CNTRL_DRV_SV__

/**
 * Component driving bootstrap pins and other misecllaneous I/O for cv32e40s core
 */
class uvma_cv32e40s_core_cntrl_drv_c extends uvma_core_cntrl_drv_c;

   `uvm_component_utils_begin(uvma_cv32e40s_core_cntrl_drv_c)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cv32e40s_core_cntrl_drv", uvm_component parent=null);

   extern task drive_bootstrap();

endclass : uvma_cv32e40s_core_cntrl_drv_c

function uvma_cv32e40s_core_cntrl_drv_c::new(string name="uvma_cv32e40s_core_cntrl_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

task uvma_cv32e40s_core_cntrl_drv_c::drive_bootstrap();

   uvma_cv32e40s_core_cntrl_cntxt_c e40s_cntxt;

   $cast(e40s_cntxt, cntxt);

   e40s_cntxt.core_cntrl_vif.boot_addr         = cfg.boot_addr;
   e40s_cntxt.core_cntrl_vif.nmi_addr          = cfg.nmi_addr;
   e40s_cntxt.core_cntrl_vif.mtvec_addr        = cfg.mtvec_addr;
   e40s_cntxt.core_cntrl_vif.dm_halt_addr      = cfg.dm_halt_addr;
   e40s_cntxt.core_cntrl_vif.dm_exception_addr = cfg.dm_exception_addr;
   e40s_cntxt.core_cntrl_vif.mhartid           = cfg.mhartid;
   e40s_cntxt.core_cntrl_vif.mimpid            = cfg.mimpid;
   e40s_cntxt.core_cntrl_vif.fetch_en          = 1'b0;
   e40s_cntxt.core_cntrl_vif.scan_cg_en        = 1'b0;

endtask : drive_bootstrap

`endif // __UVMA_CV32E40S_CORE_CNTRL_DRV_SV__
