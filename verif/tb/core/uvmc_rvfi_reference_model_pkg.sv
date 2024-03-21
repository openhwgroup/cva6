`ifndef __UVMC_RVFI_REFERENCE_MODEL_PKG_SV__
`define __UVMC_RVFI_REFERENCE_MODEL_PKG_SV__

// Pre-processor macros
`ifdef VERILATOR
`include "custom_uvm_macros.svh"
`else
`include "uvm_macros.svh"
`endif

package uvmc_rvfi_reference_model_pkg;

`ifndef VERILATOR
import uvm_pkg       ::*;
`endif
import uvma_core_cntrl_pkg::*;
import uvma_rvfi_pkg::*;

  `include "uvmc_rvfi_reference_model_utils.sv"
  `include "rvfi_spike.sv"

endpackage : uvmc_rvfi_reference_model_pkg

`endif
