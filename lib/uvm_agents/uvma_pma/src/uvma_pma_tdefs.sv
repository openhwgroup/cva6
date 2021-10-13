// Copyright 2021 OpenHW Group
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVMA_PMA_TDEFS_SV__
`define __UVMA_PMA_TDEFS_SV__

typedef enum {
   UVMA_PMA_ACCESS_INSTR,
   UVMA_PMA_ACCESS_DATA
} uvma_pma_access_enum;

typedef enum {
   UVMA_PMA_RW_WRITE,
   UVMA_PMA_RW_READ
} uvma_pma_rw_enum;

`endif // __UVMA_PMA_TDEFS_SV__
