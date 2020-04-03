// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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


`ifndef __UVML_SB_PKG_SV__
`define __UVML_SB_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
//`include "uvml_trn_macros.sv"
//`include "uvml_sb_macros.sv"


/**
 * Encapsulates all the types needed for Scoreboard library.
 */
package uvml_sb_pkg;
   
   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   
   // Constants / Structs / Enums
   `include "uvml_sb_constants.sv"
   `include "uvml_sb_tdefs.sv"
   
   // Objects
   `include "uvml_sb_cfg.sv"
   `include "uvml_sb_cntxt.sv"
   
   // Scoreboard components
   `include "uvml_sb_simplex.sv"
   
endpackage : uvml_sb_pkg


`endif // __UVML_SB_PKG_SV__
