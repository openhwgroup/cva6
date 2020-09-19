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


`ifndef __UVMA_DEBUG_PKG_SV__
`define __UVMA_DEBUG_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_debug_macros.sv"

// Interfaces / Modules / Checkers
`include "uvma_debug_if.sv"
//`include "uvma_debug_if_chk.sv"


/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring Debug.
 */
package uvma_debug_pkg;
   
   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;
   
   // Constants / Structs / Enums
   `include "uvma_debug_constants.sv"
   `include "uvma_debug_tdefs.sv"
   
   // Objects
   `include "uvma_debug_cfg.sv"
   `include "uvma_debug_cntxt.sv"
   
   // High-level transactions
   `include "uvma_debug_mon_trn.sv"
   `include "uvma_debug_mon_trn_logger.sv"
   `include "uvma_debug_seq_item.sv"
   `include "uvma_debug_seq_item_logger.sv"
   
   // Agent components
   `include "uvma_debug_cov_model.sv"
   `include "uvma_debug_drv.sv"
   `include "uvma_debug_mon.sv"
   `include "uvma_debug_sqr.sv"
   `include "uvma_debug_agent.sv"
   
   // Sequences
   `include "uvma_debug_base_seq.sv"
   `include "uvma_debug_seq_lib.sv"
   
endpackage : uvma_debug_pkg


`endif // __UVMA_DEBUG_PKG_SV__
