//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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

// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

`ifndef __UVMT_CV32E40P_PKG_SV__
`define __UVMT_CV32E40P_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvml_logs_macros.sv"
`include "uvmt_cv32e40p_macros.sv"



/**
 * Encapsulates all the types and test cases for the verification of an
 * CV32E40P RTL design.
 */
package uvmt_cv32e40p_pkg;

   import uvm_pkg::*;
   import uvme_cv32e40p_pkg::*;
   import uvml_hrtbt_pkg::*;
   import uvml_logs_pkg::*;

   // Constants / Structs / Enums
   `include "uvmt_cv32e40p_constants.sv"
   `include "uvmt_cv32e40p_tdefs.sv"

   // Virtual sequence library
   // TODO Add virtual sequences
   //      Ex: `include "uvmt_cv32e40p_sanity_vseq.sv"
   `include "uvmt_cv32e40p_vseq_lib.sv"

   // Base test case
   `include "uvmt_cv32e40p_test_cfg.sv"
   `include "uvmt_cv32e40p_test_randvars.sv"
   `include "uvmt_cv32e40p_base_test.sv"  // all testcases should extend from this testcase
   //`include "uvmt_cv32e40p_smoke_test.sv" // smoke test has multile XMRs that are illegal according to the LRM

   // Compilance tests
   `include "uvmt_cv32e40p_firmware_test.sv"

endpackage : uvmt_cv32e40p_pkg

// All Interfaces used by the CV32E40P TB are here
`include "uvmt_cv32e40p_tb_ifs.sv"

`endif // __UVMT_CV32E40P_PKG_SV__
