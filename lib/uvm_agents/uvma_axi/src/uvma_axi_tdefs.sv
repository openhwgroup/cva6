// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

`ifndef __UVMA_AXI_TDEFS_SV__
`define __UVMA_AXI_TDEFS_SV__


   typedef enum {
      UVMA_AXI_RESET_STATE_PRE_RESET,
      UVMA_AXI_RESET_STATE_IN_RESET,
      UVMA_AXI_RESET_STATE_POST_RESET
   } uvma_axi_reset_state_enum;

   typedef enum {
   UVMA_AXI_DRV_SLV_MODE_CONSTANT      ,
   UVMA_AXI_DRV_SLV_MODE_FIXED_LATENCY ,
   UVMA_AXI_DRV_SLV_MODE_RANDOM_LATENCY
   } uvma_axi_drv_slv_mode_enum;

   typedef enum {
   UVMA_AXI_DRV_SLV_ERR_MODE_OK,
   UVMA_AXI_DRV_SLV_ERR_MODE_RANDOM
   } uvma_axi_drv_slv_err_mode_enum;

`endif // __UVMA_AXI_TDEFS_SV__
