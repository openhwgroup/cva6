// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_PKG_SV__
`define __UVMA_CVXIF_PKG_SV__


// Interface(s) / Module(s) / Checker(s)
`include "uvma_cvxif_intf.sv"
`include "uvma_cvxif_assert.sv"
`include "uvma_cvxif_macros.sv"

/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring the CVXIF.
 */

package uvma_cvxif_pkg;

   import uvm_pkg ::*;

   // Constants / Structs / Enums
   `include "uvma_cvxif_constants.sv"
   `include "uvma_cvxif_tdefs.sv"

   // Objects
   `include "uvma_cvxif_cfg.sv"
   `include "uvma_cvxif_cntxt.sv"

   // High-level transactions
   `include "uvma_cvxif_req_item.sv"
   `include "uvma_cvxif_resp_item.sv"

   // Agent components
   `include "uvma_cvxif_mon.sv"
   `include "uvma_cvxif_vsqr.sv"
   `include "uvma_cvxif_drv.sv"
   `include "uvma_cvxif_cov_model.sv"
   `include "uvma_cvxif_agent.sv"

   // Virtual Sequences
   `include "uvme_cvxif_base_vseq.sv"
   `include "uvme_cvxif_vseq.sv"

endpackage : uvma_cvxif_pkg


`endif //__UVMA_CVXIF_PKG_SV__

