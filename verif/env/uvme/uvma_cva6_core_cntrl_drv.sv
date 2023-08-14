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
//

`ifndef __UVMA_CVA6_CORE_CNTRL_DRV_SV__
`define __UVMA_CVA6_CORE_CNTRL_DRV_SV__

/**
 * Component driving bootstrap pins and other misecllaneous I/O for cva6 core
 */
class uvma_cva6_core_cntrl_drv_c extends uvma_core_cntrl_drv_c;

   `uvm_component_utils_begin(uvma_cva6_core_cntrl_drv_c)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cva6_core_cntrl_drv", uvm_component parent=null);

   extern task drive_bootstrap();

endclass : uvma_cva6_core_cntrl_drv_c

function uvma_cva6_core_cntrl_drv_c::new(string name="uvma_cva6_core_cntrl_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

task uvma_cva6_core_cntrl_drv_c::drive_bootstrap();

   uvma_cva6_core_cntrl_cntxt_c cva6_cntxt;

   $cast(cva6_cntxt, cntxt);

   cva6_cntxt.core_cntrl_vif.boot_addr         = cfg.boot_addr;
   cva6_cntxt.core_cntrl_vif.nmi_addr          = cfg.nmi_addr;
   cva6_cntxt.core_cntrl_vif.mtvec_addr        = cfg.mtvec_addr;
   cva6_cntxt.core_cntrl_vif.dm_halt_addr      = cfg.dm_halt_addr;
   cva6_cntxt.core_cntrl_vif.dm_exception_addr = cfg.dm_exception_addr;
   cva6_cntxt.core_cntrl_vif.mhartid           = cfg.mhartid;
   cva6_cntxt.core_cntrl_vif.mimpid            = cfg.mimpid;
   cva6_cntxt.core_cntrl_vif.fetch_en          = 1'b0;
   cva6_cntxt.core_cntrl_vif.scan_cg_en        = 1'b0;

endtask : drive_bootstrap

`endif // __UVMA_CVA6_CORE_CNTRL_DRV_SV__
