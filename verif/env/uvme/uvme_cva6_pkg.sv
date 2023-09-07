// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
// Copyright 2021 Thales DIS Design Services SAS
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_CVA6_PKG_SV__
`define __UVME_CVA6_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvml_sb_macros.sv"

`include "uvma_clknrst_macros.sv"
`include "uvme_cva6_macros.sv"


 /**
 * Encapsulates all the types needed for an UVM environment capable of driving/
 * monitoring and verifying the behavior of an CVA6 design.
 */
package uvme_cva6_pkg;

   import uvm_pkg         ::*;
   import uvml_hrtbt_pkg  ::*;
   import uvml_sb_pkg     ::*;
   import uvml_trn_pkg    ::*;
   import uvma_clknrst_pkg::*;
   import uvma_cvxif_pkg::*;
   import uvma_axi_pkg::*;
   import uvml_mem_pkg  ::*;
   import uvma_core_cntrl_pkg::*;
   import uvma_rvfi_pkg::*;
   import uvma_isacov_pkg::*;

   // Constants / Structs / Enums
   `include "uvme_cva6_constants.sv"
   `include "uvme_cva6_tdefs.sv"

   // Objects
   `include "uvma_cva6_core_cntrl_cntxt.sv"
   `include "uvme_cva6_cfg.sv"
   `include "uvme_cva6_cntxt.sv"

   // Predictor
   `include "uvme_cva6_prd.sv"

   // Environment components
   `include "uvma_cva6_core_cntrl_drv.sv"
   `include "uvma_cva6_core_cntrl_agent.sv"
   `include "uvme_cva6_sb.sv"
   `include "uvme_cva6_vsqr.sv"
   `include "uvme_cvxif_covg.sv"
   `include "uvme_cva6_cov_model.sv"
   `include "uvme_cva6_env.sv"

   // Virtual sequences
   `include "uvme_cva6_base_vseq.sv"
   `include "uvme_cva6_reset_vseq.sv"
//   `include "uvme_cva6_interrupt_noise_vseq.sv"
   `include "uvme_cva6_vseq_lib.sv"

endpackage : uvme_cva6_pkg

`include "uvme_cva6_core_cntrl_if.sv"

`endif // __UVME_CVA6_PKG_SV__
