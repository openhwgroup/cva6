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


`ifndef __UVMA_RVVI_TDEFS_SV__
`define __UVMA_RVVI_TDEFS_SV__

typedef enum bit[MODE_WL-1:0] {
   UVMA_RVVI_U_MODE        = 0,
   UVMA_RVVI_S_MODE        = 1,
   UVMA_RVVI_RESERVED_MODE = 2,
   UVMA_RVVI_M_MODE        = 3
} uvma_rvvi_mode;

typedef enum int unsigned {
   UVMA_RVVI_STEPI = 0,
   UVMA_RVVI_TRAP  = 1,
   UVMA_RVVI_HALT  = 2
} uvma_rvvi_rm_action;

function string get_mode_str(uvma_rvvi_mode mode);
   case (mode)
      UVMA_RVVI_U_MODE: return "U";
      UVMA_RVVI_M_MODE: return "M";
      UVMA_RVVI_S_MODE: return "S";      
   endcase

   return "?";
   
endfunction : get_mode_str

`endif // __UVMA_RVVI_TDEFS_SV__
