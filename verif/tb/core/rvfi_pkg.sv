`ifndef __UVMA_RVFI_PKG_SV__
`define __UVMA_RVFI_PKG_SV__

// Pre-processor macros
`ifdef VERILATOR
    `define uvm_info(TOP,MSG,LVL) \
        begin \
            string tmp = MSG; \
            $display($sformatf("UVM_INFO @ %t ns : %s %s", $time, TOP ,tmp)); \
        end

    `define uvm_fatal(TOP,MSG) \
        begin \
            string tmp = MSG; \
            $display($sformatf("UVM_FATAL @ %t ns : %s %s", $time, TOP ,tmp)); $finish(); \
        end
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
