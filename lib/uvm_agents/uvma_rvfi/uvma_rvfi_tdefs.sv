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


`ifndef __UVMA_RVFI_TDEFS_SV__
`define __UVMA_RVFI_TDEFS_SV__

typedef enum bit[MODE_WL-1:0] {
   UVMA_RVFI_U_MODE        = 0,
   UVMA_RVFI_S_MODE        = 1,
   UVMA_RVFI_RESERVED_MODE = 2,
   UVMA_RVFI_M_MODE        = 3
} uvma_rvfi_mode;

function string get_mode_str(uvma_rvfi_mode mode);
   case (mode)
      UVMA_RVFI_U_MODE: return "U";
      UVMA_RVFI_M_MODE: return "M";
      UVMA_RVFI_S_MODE: return "S";
   endcase

   return "?";

endfunction : get_mode_str

`endif // __UVMA_RVFI_TDEFS_SV__
