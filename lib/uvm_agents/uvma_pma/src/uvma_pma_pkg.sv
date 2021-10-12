// Copyright 2021 OpenHW Group
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVMA_PMA_PKG_SV__
`define __UVMA_PMA_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_pma_macros.sv"


/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or monitoring Memory attribution agent for OpenHW Group CORE-V verification testbenches.
 */
package uvma_pma_pkg;

   import uvm_pkg            ::*;
   import uvml_hrtbt_pkg     ::*;
   import uvml_trn_pkg       ::*;
   import uvml_logs_pkg      ::*;
   import uvma_core_cntrl_pkg::*;
   import uvma_obi_memory_pkg::*;
   import uvma_rvfi_pkg      ::*;

   `uvm_analysis_imp_decl(_rvfi_instr)
   `uvm_analysis_imp_decl(_obi_i)
   `uvm_analysis_imp_decl(_obi_d)

   // Constants / Structs / Enums
   `include "uvma_pma_constants.sv"
   `include "uvma_pma_tdefs.sv"

   // Objects
   `include "uvma_pma_cfg.sv"
   `include "uvma_pma_cntxt.sv"

   // High-level transactions
   `include "uvma_pma_mon_trn.sv"
   `include "uvma_pma_mon_trn_logger.sv"

   // Agent components
   `include "uvma_pma_cov_model.sv"
   `include "uvma_pma_region_cov_model.sv"
   `include "uvma_pma_sb.sv"
   `include "uvma_pma_mon.sv"
   `include "uvma_pma_agent.sv"

endpackage : uvma_pma_pkg


`endif // __UVMA_PMA_PKG_SV__
