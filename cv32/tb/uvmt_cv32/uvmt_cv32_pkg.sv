// COPYRIGHT HEADER


`ifndef __UVMT_CV32_PKG_SV__
`define __UVMT_CV32_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvmt_cv32_macros.sv"

// Time units and precision for this test bench
timeunit       1ns;
timeprecision  1ps;

// Interfaces
`include "uvmt_cv32_clk_gen_if.sv"


/**
 * Encapsulates all the types and test cases for the verification of an
 * CV32 RTL design.
 */
package uvmt_cv32_pkg;
   
   import uvm_pkg::*;
   import uvml_hrtbt_pkg::*;
   import uvml_logs_pkg::*;
   import uvma_debug_pkg::*;
   import uvma_reset_pkg::*;
   import uvme_cv32_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvmt_cv32_constants.sv"
   `include "uvmt_cv32_tdefs.sv"
   
   // Virtual sequence library
   // TODO Add virtual sequences
   //      Ex: `include "uvmt_cv32_sanity_vseq.sv"
   `include "uvmt_cv32_vseq_lib.sv"
   
   // Base test case
   `include "uvmt_cv32_test_cfg.sv"
   `include "uvmt_cv32_base_test.sv"
   
   // Functional tests
   `include "uvmt_cv32_reg_base_test.sv"
   `include "uvmt_cv32_reg_hw_reset_test.sv"
   `include "uvmt_cv32_reg_bit_bash_test.sv"
   
endpackage : uvmt_cv32_pkg


`endif // __UVMT_CV32_PKG_SV__
