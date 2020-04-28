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

module dut
#(
    parameter ID         = 0,
    parameter VENDOR     = "riscv.ovpworld.org",
    parameter VARIANT    = "RV32GC",
    parameter COMPARE    = 0,
    parameter STOPONTRAP = 1
);
    
    BUS         b1();
    
    MONITOR     #(.ID(ID),
                  .VARIANT(VARIANT),
                  .STOPONTRAP(STOPONTRAP))
                  mon(b1);
    RAM         ram(b1);
    INTC        intc(b1);
    
    CPU #(
        .ID(ID), 
        .VENDOR(VENDOR), 
        .VARIANT(VARIANT),
        .COMPARE(COMPARE))
        cpu(b1);
    
    reg Clk;
    assign Clk = b1.Clk;
    
    reg [31:0] Addr;
    assign Addr = b1.Addr;

    reg [31:0] Data;
    assign Data = b1.Data;
    
    reg [2:0] Size;
    assign Size = b1.Size;

    reg [1:0] Transfer;
    assign Transfer = b1.Transfer;
    
    reg Load, Store, Fetch;
    
    always @Transfer begin
        Load  = (Transfer == 1) ? 1 : 0;
        Store = (Transfer == 2) ? 1 : 0;
        Fetch = (Transfer == 3) ? 1 : 0;
    end
    
    initial begin
        b1.Clk = 0;
        forever begin
            #10 b1.Clk <= ~b1.Clk;
        end
    end

endmodule
