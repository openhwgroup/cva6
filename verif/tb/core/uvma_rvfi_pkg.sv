`ifndef __UVMA_RVFI_PKG_SV__
`define __UVMA_RVFI_PKG_SV__

// Pre-processor macros
`ifdef VERILATOR
`include "custom_uvm_macros.svh"
`else
`include "uvm_macros.svh"
`endif

package uvma_rvfi_pkg;

`ifndef VERILATOR
import uvm_pkg       ::*;
`endif
import uvma_core_cntrl_pkg::*;

`include "uvma_rvfi_constants.sv"
`include "uvma_rvfi_tdefs.sv"

endpackage : uvma_rvfi_pkg

`endif
