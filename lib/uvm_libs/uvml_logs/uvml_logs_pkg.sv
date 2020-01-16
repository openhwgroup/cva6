// COPYRIGHT HEADER


`ifndef __UVML_LOGS_PKG_SV__
`define __UVML_LOGS_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_logs_macros.sv"


/**
 * Encapsulates all the types needed for Logs library.
 */
package uvml_logs_pkg;
   
   import uvm_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvml_logs_constants.sv"
   `include "uvml_logs_tdefs.sv"
   
endpackage : uvml_logs_pkg


`endif // __UVML_LOGS_PKG_SV__
