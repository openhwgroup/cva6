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

`ifndef __UVMA_CORE_CNTRL_PKG_SV__
`define __UVMA_CORE_CNTRL_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_core_cntrl_macros.sv"

/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring Clock & Reset.
 */
package uvma_core_cntrl_pkg;

   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;

   // Forward decl of sequencer for p_sequencer delcaration
   typedef class uvma_core_cntrl_sqr_c;

   // Constants / Structs / Enums
   `include "uvma_core_cntrl_constants.sv"
   `include "uvma_core_cntrl_tdefs.sv"
   
   // Objects
   `include "uvma_core_cntrl_pma_region.sv"
   `include "uvma_core_cntrl_cntxt.sv"
   `include "uvma_core_cntrl_cfg.sv"

   // Sequences
   `include "seq/uvma_core_cntrl_base_seq.sv"

   // High-level transactions
   // `include "seq/uvma_core_cntrl_state_seq_item.sv"
   // `include "seq/uvma_core_cntrl_control_seq_item.sv"
   // `include "uvma_core_cntrl_mon_trn_logger.sv"
   
   // Agent components   
   `include "uvma_core_cntrl_sqr.sv"
   `include "uvma_core_cntrl_drv.sv"
   `include "uvma_core_cntrl_agent.sv"
      
endpackage : uvma_core_cntrl_pkg

`endif // __UVMA_CORE_CNTRL_PKG_SV__
