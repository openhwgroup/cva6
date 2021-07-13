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


`ifndef __UVMA_CORE_CNTRL_CONSTANTS_SV__
`define __UVMA_CORE_CNTRL_CONSTANTS_SV__

localparam CSR_ADDR_WL = 12;
localparam CSR_MASK_WL = (1 << CSR_ADDR_WL);

localparam MAX_XLEN   = 128;

localparam MAX_NUM_MHPMCOUNTERS = 29;
localparam MAX_NUM_HPMCOUNTERS  = 29;

`endif // __UVMA_CORE_CNTRL_CONSTANTS_SV__

