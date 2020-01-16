// COPYRIGHT HEADER


`ifndef __UVMA_DEBUG_PKG_SV__
`define __UVMA_DEBUG_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_debug_macros.sv"

// Interfaces / Modules / Checkers
`include "uvma_debug_if.sv"
//`include "uvma_debug_if_chk.sv"


/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring Debug.
 */
package uvma_debug_pkg;
   
   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;
   import uvma_reset_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvma_debug_constants.sv"
   `include "uvma_debug_tdefs.sv"
   
   // Objects
   `include "uvma_debug_cfg.sv"
   `include "uvma_debug_cntxt.sv"
   
   // High-level transactions
   `include "uvma_debug_mon_trn.sv"
   `include "uvma_debug_mon_trn_logger.sv"
   `include "uvma_debug_seq_item.sv"
   `include "uvma_debug_seq_item_logger.sv"
   
   // Agent components
   `include "uvma_debug_cov_model.sv"
   `include "uvma_debug_drv.sv"
   `include "uvma_debug_mon.sv"
   `include "uvma_debug_sqr.sv"
   `include "uvma_debug_agent.sv"
   
   // Sequences
   `include "uvma_debug_base_seq.sv"
   `include "uvma_debug_seq_lib.sv"
   
endpackage : uvma_debug_pkg


`endif // __UVMA_DEBUG_PKG_SV__
