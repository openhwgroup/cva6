// COPYRIGHT HEADER


`ifndef __UVML_HRTBT_PKG_SV__
`define __UVML_HRTBT_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"


/**
 * Encapsulates all the types needed for Heartbeat library.
 */
package uvml_hrtbt_pkg;
   
   import uvm_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvml_hrtbt_constants.sv"
   `include "uvml_hrtbt_tdefs.sv"
   
endpackage : uvml_hrtbt_pkg


`endif // __UVML_HRTBT_PKG_SV__
