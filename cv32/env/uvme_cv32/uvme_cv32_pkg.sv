// COPYRIGHT HEADER


`ifndef __UVME_CV32_PKG_SV__
`define __UVME_CV32_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvme_cv32_macros.sv"


 /**
 * Encapsulates all the types needed for an UVM environment capable of driving/
 * monitoring and verifying the behavior of an CV32 design.
 */
package uvme_cv32_pkg;
   
   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_sb_pkg   ::*;
   import uvma_debug_pkg::*;
   import uvma_reset_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvme_cv32_constants.sv"
   `include "uvme_cv32_tdefs.sv"
   
   // Register Abstraction Layer
   `include "uvme_cv32_ral.sv"
   
   // Objects
   `include "uvme_cv32_cfg.sv"
   `include "uvme_cv32_cntxt.sv"
   
   // Predictor
   `include "uvme_cv32_prd.sv"
   
   // Environment components
   `include "uvme_cv32_cov_model.sv"
   `include "uvme_cv32_sb.sv"
   `include "uvme_cv32_vsqr.sv"
   `include "uvme_cv32_env.sv"
   
   // Virtual sequences
   `include "uvme_cv32_base_vseq.sv"
   `include "uvme_cv32_reg_base_vseq.sv"
   `include "uvme_cv32_reg_bit_bash_vseq.sv"
   `include "uvme_cv32_reg_hw_reset_vseq.sv"
   `include "uvme_cv32_vseq_lib.sv"
   
endpackage : uvme_cv32_pkg


`endif // __UVME_CV32_PKG_SV__
