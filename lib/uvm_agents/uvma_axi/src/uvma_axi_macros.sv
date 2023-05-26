// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

`ifndef __UVMA_AXI_MACROS_SV__
`define __UVMA_AXI_MACROS_SV__

   parameter Nr_Slaves      = 2;  // actually masters, but slaves on the crossbar
   parameter Id_Width       = 4;  // 4 is recommended by AXI standard, so lets stick to it, do not change
   parameter Id_Width_Slave = Id_Width + $clog2(Nr_Slaves);

   `define UVMA_AXI_ADDR_MAX_WIDTH           64
   `define UVMA_AXI_DATA_MAX_WIDTH           64
   `define UVMA_AXI_USER_MAX_WIDTH            1
   `define UVMA_AXI_ID_MAX_WIDTH              Id_Width_Slave
   `define UVMA_AXI_STRB_MAX_WIDTH            8

   `define per_instance_fcov `ifndef DSIM option.per_instance = 1; `endif

`endif // __UVMA_AXI_MACROS_SV__
