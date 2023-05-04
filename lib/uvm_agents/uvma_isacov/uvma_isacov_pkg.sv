// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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


`include "uvma_isacov_macros.sv"

package uvma_isacov_pkg;

  import uvm_pkg::*;
  import uvml_trn_pkg::*;
  import uvml_logs_pkg::*;
  import uvma_core_cntrl_pkg::*;
  import uvma_rvfi_pkg::*;

  // DPI imports
  `include "dpi_dasm_imports.svh"

  // Constants / Structs / Enums  
  `include "uvma_isacov_constants.sv"
  `include "uvma_isacov_tdefs.sv"

  // Objects
  `include "uvma_isacov_cfg.sv"
  `include "uvma_isacov_cntxt.sv"
  `include "uvma_isacov_instr.sv"

  // Transactions
  `include "uvma_isacov_mon_trn.sv"
  `include "uvma_isacov_mon_trn_logger.sv"

  // Components
  `include "uvma_isacov_cov_model.sv"
  `include "uvma_isacov_mon.sv"
  `include "uvma_isacov_agent.sv"

endpackage : uvma_isacov_pkg
