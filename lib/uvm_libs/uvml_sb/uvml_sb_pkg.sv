// COPYRIGHT HEADER


`ifndef __UVML_SB_PKG_SV__
`define __UVML_SB_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_sb_macros.sv"


/**
 * Encapsulates all the types needed for Scoreboard library.
 */
package uvml_sb_pkg;
   
   import uvm_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvml_sb_constants.sv"
   `include "uvml_sb_tdefs.sv"
   
endpackage : uvml_sb_pkg


`endif // __UVML_SB_PKG_SV__
