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


`ifndef __UVMA_RVFI_CONSTANTS_SV__
`define __UVMA_RVFI_CONSTANTS_SV__

// RVFI field widths
localparam ORDER_WL         = 64;
localparam MODE_WL          = 2;
localparam IXL_WL           = 2;
localparam TRAP_WL          = 12;
localparam GPR_ADDR_WL      = 5;
localparam RVFI_DBG_WL      = 3;
localparam RVFI_NMIP_WL     = 2;
localparam CYCLE_CNT_WL     = 32;

// Fields within TRAP
localparam TRAP_EXCP_LSB         = 0;
localparam TRAP_EXCP_WL          = 1;
localparam TRAP_NONDBG_ENTRY_LSB = 1;
localparam TRAP_NONDBG_ENTRY_WL  = 1;
localparam TRAP_DBG_ENTRY_LSB    = 2;
localparam TRAP_DBG_ENTRY_WL     = 1;
localparam TRAP_CAUSE_LSB        = 3;
localparam TRAP_CAUSE_WL         = 6;
localparam TRAP_DBG_CAUSE_LSB    = 9;
localparam TRAP_DBG_CAUSE_WL     = 3;

localparam DEFAULT_ILEN     = 32;
localparam DEFAULT_XLEN     = 32;
localparam DEFAULT_NRET     = 1;


`endif // __UVMA_RVFI_CONSTANTS_SV__
