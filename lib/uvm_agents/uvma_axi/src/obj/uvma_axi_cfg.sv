// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi


`ifndef __UVMA_AXI_CFG_SV__
`define __UVMA_AXI_CFG_SV__

class uvma_axi_cfg_c extends uvm_object;

   rand uvm_active_passive_enum            is_active;


   `uvm_object_utils_begin(uvma_axi_cfg_c)
      `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT);
   `uvm_object_utils_end

   constraint defaults_config {
      soft is_active                   == UVM_ACTIVE;
     }

   extern function new(string name = "uvma_axi_cfg");

endclass : uvma_axi_cfg_c


function uvma_axi_cfg_c::new(string name = "uvma_axi_cfg");

   super.new(name);

endfunction : new

`endif //__UVMA_AXI_CFG_SV__
