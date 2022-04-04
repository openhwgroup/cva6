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


`ifndef __UVMA_RVFI_PKG_SV__
`define __UVMA_RVFI_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_rvfi_macros.sv"

/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring Clock & Reset.
 */
package uvma_rvfi_pkg;

   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;
   import uvma_core_cntrl_pkg::*;
   
   // Analysis implementation declarations
   `uvm_analysis_imp_decl(_rvfi_instr)

   // Constants / Structs / Enums
   `include "uvma_rvfi_constants.sv"
   `include "uvma_rvfi_tdefs.sv"
   
   // Objects
   `include "uvma_rvfi_cfg.sv"
   `include "uvma_rvfi_cntxt.sv"
   
   // High-level transactions
   `include "seq/uvma_rvfi_csr_seq_item.sv"   
   `include "seq/uvma_rvfi_instr_seq_item.sv"
   `include "seq/uvma_rvfi_instr_table_seq_item.sv"
      
   // Agent components   
   `include "uvma_rvfi_mon_trn_logger.sv"
   `include "uvma_rvfi_instr_mon.sv"   
   `include "uvma_rvfi_agent.sv"
      
endpackage : uvma_rvfi_pkg

// Interface(s) / Module(s) / Checker(s)
`include "uvma_rvfi_instr_if.sv"
`include "uvma_rvfi_csr_if.sv"
`include "uvma_rvfi_assert.sv"

`endif // __UVMA_RVFI_PKG_SV__


