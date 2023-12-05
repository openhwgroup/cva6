// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

`ifndef __UVMA_INTERRUPT_TDEFS_SV__
`define __UVMA_INTERRUPT_TDEFS_SV__

typedef enum {
   UVMA_INTERRUPT_ONE_BY_ONE,
   UVMA_INTERRUPT_MORE_THAN_ONE,
   UVMA_INTERRUPT_RANDOMIZE
} uvma_interrupt_cntrl_enum;

typedef enum {
   UVMA_INTERRUPT_DRV_REQ_MODE_CONSTANT,
   UVMA_INTERRUPT_DRV_REQ_MODE_FIXED_LATENCY,
   UVMA_INTERRUPT_DRV_REQ_MODE_RANDOM_LATENCY
} uvma_interrupt_drv_req_enum;

`endif // __UVMA_INTERRUPT_TDEFS_SV__
