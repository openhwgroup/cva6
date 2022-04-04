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

`ifndef __UVMA_RVVI_PKG_SV__
`define __UVMA_RVVI_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_rvvi_macros.sv"

/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring Clock & Reset.
 */
package uvma_rvvi_pkg;

   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;
   import uvma_core_cntrl_pkg::*;
   import uvma_obi_memory_pkg::*;
   import uvma_rvfi_pkg ::*;
   

   // Forward decl of sequencer for p_sequencer delcaration
   typedef class uvma_rvvi_sqr_c;

   // Constants / Structs / Enums
   `include "uvma_rvvi_constants.sv"
   `include "uvma_rvvi_tdefs.sv"
   
   // Objects
   `include "uvma_rvvi_cfg.sv"
   `include "uvma_rvvi_cntxt.sv"
   
   // High-level transactions
   `include "seq/uvma_rvvi_state_seq_item.sv"
   `include "seq/uvma_rvvi_control_seq_item.sv"
   `include "uvma_rvvi_mon_trn_logger.sv"
   
   // Sequences
   `include "seq/uvma_rvvi_base_seq.sv"
   `include "seq/uvma_rvvi_control_seq.sv"

   // Agent components   
   `include "uvma_rvvi_state_mon.sv"
   `include "uvma_rvvi_sqr.sv"
   `include "uvma_rvvi_drv.sv"
   `include "uvma_rvvi_agent.sv"
      
endpackage : uvma_rvvi_pkg

// Interface(s) / Module(s) / Checker(s)
//`include "uvma_rvvi_csr_if.sv"

`endif // __UVMA_RVVI_PKG_SV__
