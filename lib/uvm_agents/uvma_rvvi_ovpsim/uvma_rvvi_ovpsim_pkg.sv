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

`ifndef __UVMA_RVVI_OVPSIM_PKG_SV__
`define __UVMA_RVVI_OVPSIM_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_rvvi_ovpsim_macros.sv"

/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring Clock & Reset.
 */
package uvma_rvvi_ovpsim_pkg;

   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;
   import uvma_clknrst_pkg::*;
   import uvma_core_cntrl_pkg::*;
   import uvma_rvfi_pkg ::*;
   import uvma_rvvi_pkg ::*;

   // Constants / Structs / Enums
   `include "uvma_rvvi_ovpsim_constants.sv"
   `include "uvma_rvvi_ovpsim_tdefs.sv"

   // Objects
   `include "uvma_rvvi_ovpsim_cfg.sv"
   `include "uvma_rvvi_ovpsim_cntxt.sv"

   // High-level transactions
   `include "seq/uvma_rvvi_ovpsim_control_seq_item.sv"

   // Sequences
   `include "seq/uvma_rvvi_ovpsim_control_seq.sv"

   // Agent components
   `include "uvma_rvvi_ovpsim_state_mon.sv"
   `include "uvma_rvvi_ovpsim_drv.sv"
   `include "uvma_rvvi_ovpsim_agent.sv"

endpackage : uvma_rvvi_ovpsim_pkg

`endif // __UVMA_RVVI_OVPSIM_PKG_SV__
