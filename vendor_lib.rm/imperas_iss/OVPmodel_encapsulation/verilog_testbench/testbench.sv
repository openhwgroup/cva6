/*
 *
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 *
 * The contents of this file are provided under the Software License
 * Agreement that you accepted before downloading this file.
 *
 * This source forms part of the Software and can be used for educational,
 * training, and demonstration purposes but cannot be used for derivative
 * works except in cases where the derivative works require OVP technology
 * to run.
 *
 * For open source models released under licenses that you can use for
 * derivative works, please visit www.OVPworld.org or www.imperas.com
 * for the location of the open source models.
 *
 */

`ifdef COVERAGE
`include "class_simple_coverage.svh" 
`endif

//
// Execute single dut instance
//
`ifndef T0_TYPE
  `define T0_TYPE "RV32GC"
`endif
module tb_single;
    dut #(
        .ID(0), 
        .VENDOR("riscv.ovpworld.org"), 
        .VARIANT(`T0_TYPE), 
        .COMPARE(0),
        .STOPONTRAP(1)) 
        t0();
    
`ifdef COVERAGE
    coverage cov1;
    initial begin
        cov1 = new();
    end
    
    always @t0.cpu.Retire begin
        if (t0.cpu.mode_disass == 1) begin
            cov1.sample(t0.cpu.Decode);
        end
    end
`endif
	
    initial if ($test$plusargs("dumpvars")) $dumpvars();
endmodule

