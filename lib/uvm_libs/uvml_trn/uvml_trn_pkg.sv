// COPYRIGHT HEADER


`ifndef __UVML_TRN_PKG_SV__
`define __UVML_TRN_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_trn_macros.sv"


/**
 * Encapsulates all the types needed for Transaction library.
 */
package uvml_trn_pkg;
   
   import uvm_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvml_trn_constants.sv"
   `include "uvml_trn_tdefs.sv"
   
endpackage : uvml_trn_pkg


`endif // __UVML_TRN_PKG_SV__
