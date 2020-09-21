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


`ifndef __UVME_CV32_PKG_SV__
`define __UVME_CV32_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvml_sb_macros.sv"

`include "uvma_clknrst_macros.sv"
`include "uvme_cv32_macros.sv"


 /**
 * Encapsulates all the types needed for an UVM environment capable of driving/
 * monitoring and verifying the behavior of an CV32 design.
 */
package uvme_cv32_pkg;
   
   import uvm_pkg         ::*;
   import uvml_hrtbt_pkg  ::*;
   import uvml_sb_pkg     ::*;
   import uvml_trn_pkg    ::*;  
   import uvma_clknrst_pkg::*;
   import uvma_interrupt_pkg::*;
   import uvma_debug_pkg::*;
   import uvma_obi_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvme_cv32_constants.sv"
   `include "uvme_cv32_tdefs.sv"
   
   // Register Abstraction Layer
   `include "uvme_cv32_ral.sv"
   
   // Objects
   `include "uvme_cv32_cfg.sv"
   `include "uvme_cv32_cntxt.sv"
   `include "uvme_rv32isa_covg_trn.sv"

   // Predictor
   `include "uvme_cv32_prd.sv"
   
   // Environment components
   `include "uvme_interrupt_covg.sv"
   `include "uvme_debug_covg.sv"
   `include "uvme_rv32isa_covg.sv"
   `include "uvme_cv32_cov_model.sv"
   `include "uvme_cv32_sb.sv"
   `include "uvme_cv32_vsqr.sv"
   `include "uvme_cv32_env.sv"
   
   // Virtual sequences
   `include "uvme_cv32_base_vseq.sv"
   `include "uvme_cv32_reset_vseq.sv"
   `include "uvme_cv32_interrupt_noise_vseq.sv"
   `include "uvme_cv32_reg_base_vseq.sv"
   `include "uvme_cv32_reg_bit_bash_vseq.sv"
   `include "uvme_cv32_reg_hw_reset_vseq.sv"
   `include "uvme_cv32_vseq_lib.sv"
   `include "uvme_cv32_random_debug_vseq.sv" 
endpackage : uvme_cv32_pkg


`endif // __UVME_CV32_PKG_SV__
