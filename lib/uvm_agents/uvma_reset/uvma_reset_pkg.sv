// COPYRIGHT HEADER


`ifndef __UVMA_RESET_PKG_SV__
`define __UVMA_RESET_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_reset_macros.sv"

// Interfaces / Modules / Checkers
`include "uvma_reset_if.sv"
//`include "uvma_reset_if_chk.sv"


/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring Reset.
 */
package uvma_reset_pkg;
   
   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;
   import uvma_reset_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvma_reset_constants.sv"
   `include "uvma_reset_tdefs.sv"
   
   // Objects
   `include "uvma_reset_cfg.sv"
   `include "uvma_reset_cntxt.sv"
   
   // High-level transactions
   `include "uvma_reset_mon_trn.sv"
   `include "uvma_reset_mon_trn_logger.sv"
   `include "uvma_reset_seq_item.sv"
   `include "uvma_reset_seq_item_logger.sv"
   
   // Agent components
   `include "uvma_reset_cov_model.sv"
   `include "uvma_reset_drv.sv"
   `include "uvma_reset_mon.sv"
   `include "uvma_reset_sqr.sv"
   `include "uvma_reset_agent.sv"
   
   // Sequences
   `include "uvma_reset_base_seq.sv"
   `include "uvma_reset_seq_lib.sv"
   
endpackage : uvma_reset_pkg


`endif // __UVMA_RESET_PKG_SV__
