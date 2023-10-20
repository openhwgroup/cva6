`ifndef __UVMA_RVFI_PKG_SV__
`define __UVMA_RVFI_PKG_SV__

// Pre-processor macros
`ifdef VERILATOR
    `define uvm_info(TOP,MSG,LVL) \
        $display(TOP + ":" + MSG);
    `define uvm_fatal(TOP,MSG) \
        $display(TOP + ":" + MSG); $finish();
`else
`include "uvm_macros.svh"
`endif

package rvfi_pkg;

`ifndef VERILATOR
import uvm_pkg       ::*;
`endif


`include "uvma_rvfi_constants.sv"
`include "uvma_rvfi_tdefs.sv"
`include "uvma_rvfi_utils.sv"

endpackage

`endif
