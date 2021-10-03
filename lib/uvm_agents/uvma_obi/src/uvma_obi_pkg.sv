// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// Copyright 2021 Silicon Labs
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef __UVMA_OBI_PKG_SV__
`define __UVMA_OBI_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_macros.sv"
`include "uvml_logs_macros.sv"
`include "uvml_mem_macros.sv"
`include "uvma_obi_macros.sv"

// Interface(s)
`include "uvma_obi_if.sv"


/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or monitoring Open Bus Interface.
 */
package uvma_obi_pkg;
   
   import uvm_pkg      ::*;
   import uvml_pkg     ::*;
   import uvml_logs_pkg::*;
   import uvml_mem_pkg ::*;
   
   // Constants / Structs / Enums
   `include "uvma_obi_tdefs.sv"
   `include "uvma_obi_constants.sv"
   
   // Objects
   `include "uvma_obi_cfg.sv"
   `include "uvma_obi_cntxt.sv"
   
   // Monitor Transactions
   `include "uvma_obi_mon_trn.sv"
   `include "uvma_obi_mstr_a_mon_trn.sv"
   `include "uvma_obi_mstr_r_mon_trn.sv"
   `include "uvma_obi_slv_a_mon_trn.sv"
   `include "uvma_obi_slv_r_mon_trn.sv"
   
   // Sequence Items
   `include "uvma_obi_seq_item.sv"
   `include "uvma_obi_mstr_a_seq_item.sv"
   `include "uvma_obi_mstr_r_seq_item.sv"
   `include "uvma_obi_slv_a_seq_item.sv"
   `include "uvma_obi_slv_r_seq_item.sv"
   
   // Logger
   `include "uvma_obi_mon_trn_logger.sv"
   `include "uvma_obi_mstr_a_mon_trn_logger.sv"
   `include "uvma_obi_mstr_r_mon_trn_logger.sv"
   `include "uvma_obi_slv_a_mon_trn_logger.sv"
   `include "uvma_obi_slv_r_mon_trn_logger.sv"
   `include "uvma_obi_seq_item_logger.sv"
   `include "uvma_obi_mstr_a_seq_item_logger.sv"
   `include "uvma_obi_mstr_r_seq_item_logger.sv"
   `include "uvma_obi_slv_a_seq_item_logger.sv"
   `include "uvma_obi_slv_r_seq_item_logger.sv"
   
   // Virtual sequencer
   `include "uvma_obi_mstr_a_sqr.sv"
   `include "uvma_obi_mstr_r_sqr.sv"
   `include "uvma_obi_slv_a_sqr.sv"
   `include "uvma_obi_slv_r_sqr.sv"
   
   // Driver
   `include "uvma_obi_mstr_a_drv.sv"
   `include "uvma_obi_mstr_r_drv.sv"
   `include "uvma_obi_slv_a_drv.sv"
   `include "uvma_obi_slv_r_drv.sv"
   
   // Agent top-level components
   `include "uvma_obi_mon.sv"
   `include "uvma_obi_drv.sv"
   `include "uvma_obi_vsqr.sv"
   `include "uvma_obi_logger.sv"
   `include "uvma_obi_cov_model.sv"
   `include "uvma_obi_agent.sv"
   
   // Sequences
   `include "uvma_obi_base_vseq.sv"
   `include "uvma_obi_mon_vseq.sv"
   `include "uvma_obi_idle_vseq.sv"
   `include "uvma_obi_mstr_vseq.sv"
   `include "uvma_obi_slv_vseq.sv"
   `include "uvma_obi_slv_handler_base_vseq.sv"
   `include "uvma_obi_slv_handler_mem_vseq.sv"
   
endpackage : uvma_obi_pkg


// Module(s) / Checker(s)
`ifdef UVMA_OBI_INC_CHKR
`include "uvma_obi_chkr.sv"
`endif


`endif // __UVMA_OBI_PKG_SV__
