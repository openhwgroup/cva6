// 
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
// 


`ifndef __UVMA_OBI_PKG_SV__
`define __UVMA_OBI_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_obi_macros.sv"

// Interface(s) / Module(s) / Checker(s)
`include "uvma_obi_if.sv"

/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring Clock & Reset.
 */
package uvma_obi_pkg;

   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;

   // Constants / Structs / Enums
   `include "uvma_obi_constants.sv"
   `include "uvma_obi_tdefs.sv"
   
   // Objects
   `include "uvma_obi_cfg.sv"
   `include "uvma_obi_cntxt.sv"
   
   // High-level transactions
   `include "uvma_obi_seq_item.sv"
   `include "uvma_obi_seq_item_logger.sv"
   `include "uvma_obi_mon_trn.sv"
   `include "uvma_obi_mon_trn_logger.sv"
   
   // Agent components
   `include "uvma_obi_cov_model.sv"
   `include "uvma_obi_drv.sv"
   `include "uvma_obi_mon.sv"
   `include "uvma_obi_sqr.sv"
   `include "uvma_obi_agent.sv"
   
   // Sequences
   `include "uvma_obi_base_seq.sv"
   `include "uvma_obi_seq_lib.sv"
   
endpackage : uvma_obi_pkg


`endif // __UVMA_OBI_PKG_SV__
