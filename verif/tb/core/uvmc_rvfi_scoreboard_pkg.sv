`ifndef __UVMC_RVFI_SCOREBOARD_PKG_SV__
`define __UVMC_RVFI_SCOREBOARD_PKG_SV__

// Pre-processor macros
`ifdef VERILATOR
`include "custom_uvm_macros.svh"
`else
`include "uvm_macros.svh"
`endif

package uvmc_rvfi_scoreboard_pkg;

`ifndef VERILATOR
import uvm_pkg       ::*;
`endif
import uvma_core_cntrl_pkg::*;
import uvmc_rvfi_reference_model_pkg::*;
import uvma_rvfi_pkg::*;

// DPI imports
`include "dpi_dasm_imports.svh"

`include "uvma_rvfi_constants.sv"
`include "uvmc_rvfi_scoreboard_utils.sv"

endpackage : uvmc_rvfi_scoreboard_pkg

`endif
