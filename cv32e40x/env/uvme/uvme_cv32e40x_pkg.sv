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


`ifndef __UVME_CV32E40X_PKG_SV__
`define __UVME_CV32E40X_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvml_sb_macros.sv"

`include "uvma_clknrst_macros.sv"
`include "uvme_cv32e40x_macros.sv"


 /**
 * Encapsulates all the types needed for an UVM environment capable of driving/
 * monitoring and verifying the behavior of an CV32E40X design.
 */
package uvme_cv32e40x_pkg;

   import uvm_pkg         ::*;
   import uvml_hrtbt_pkg  ::*;
   import uvml_sb_pkg     ::*;
   import uvml_trn_pkg    ::*;
   import uvml_mem_pkg    ::*;
   import uvma_core_cntrl_pkg::*;
   import uvma_isacov_pkg::*;
   import uvma_clknrst_pkg::*;
   import uvma_interrupt_pkg::*;
   import uvma_debug_pkg::*;
   import uvma_obi_memory_pkg::*;
   import uvma_rvfi_pkg::*;
   import uvma_rvvi_pkg::*;
   import uvma_rvvi_ovpsim_pkg::*;
   import uvma_fencei_pkg::*;
   import uvma_pma_pkg::*;

   // Forward decls
   typedef class uvme_cv32e40x_vsqr_c;

   // Constants / Structs / Enums
   `include "uvme_cv32e40x_constants.sv"
   `include "uvme_cv32e40x_tdefs.sv"

   // Objects
   `include "uvma_cv32e40x_core_cntrl_cntxt.sv"
   `include "uvme_cv32e40x_cfg.sv"
   `include "uvme_cv32e40x_cntxt.sv"

   // Predictor
   `include "uvme_cv32e40x_prd.sv"

   // Virtual sequences
   `include "uvme_cv32e40x_base_vseq.sv"
   `include "uvme_cv32e40x_reset_vseq.sv"
   `include "uvme_cv32e40x_vp_debug_control_seq.sv"
   `include "uvme_cv32e40x_vp_interrupt_timer_seq.sv"
   `include "uvme_cv32e40x_vp_sig_writer_seq.sv"
   `include "uvme_cv32e40x_vp_status_flags_seq.sv"
   `include "uvme_cv32e40x_vp_fencei_tamper_seq.sv"
   `include "uvme_cv32e40x_interrupt_noise_vseq.sv"
   `include "uvme_cv32e40x_vseq_lib.sv"
   `include "uvme_cv32e40x_core_cntrl_base_seq.sv"
   `include "uvme_cv32e40x_core_cntrl_fetch_toggle_seq.sv"
   `include "uvme_cv32e40x_random_debug_vseq.sv"
   `include "uvme_cv32e40x_random_debug_reset_vseq.sv"
   `include "uvme_cv32e40x_random_debug_bootset_vseq.sv"

   // Environment components
   `include "uvma_cv32e40x_core_cntrl_drv.sv"
   `include "uvma_cv32e40x_core_cntrl_agent.sv"
   `include "uvme_interrupt_covg.sv"
   `include "uvme_debug_covg.sv"
   `include "uvme_exceptions_covg.sv"
   `include "uvme_counters_covg.sv"
   `include "uvme_cv32e40x_cov_model.sv"
   `include "uvme_cv32e40x_sb.sv"
   `include "uvme_cv32e40x_core_sb.sv"
   `include "uvme_cv32e40x_buserr_sb.sv"
   `include "uvme_cv32e40x_vsqr.sv"
   `include "uvme_cv32e40x_env.sv"

endpackage : uvme_cv32e40x_pkg

// Interfaces
`include "uvme_cv32e40x_core_cntrl_if.sv"

`endif // __UVME_CV32E40X_PKG_SV__


