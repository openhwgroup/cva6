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
    parameter int ROM_START_ADDR = 'h8000,
    parameter int ROM_BYTE_SIZE  = 'h20000,
    parameter int RAM_BYTE_SIZE  = 'h20000,
    parameter int ID = 0
);
    
    BUS         b1();
    
    MONITOR     mon(b1);
    RAM         #(
                .ROM_START_ADDR(ROM_START_ADDR),
                .ROM_BYTE_SIZE(ROM_BYTE_SIZE),
                .RAM_BYTE_SIZE(RAM_BYTE_SIZE)) ram(b1);
   
    CPU #(.ID(ID)) cpu(b1);
    
    reg Clk;
    assign Clk = b1.Clk;
    
    reg [31:0] DAddr, IAddr;
    assign DAddr = b1.DAddr;
    assign IAddr = b1.IAddr;

    reg [31:0] DData, IData;
    assign DData = b1.DData;
    assign IData = b1.IData;
    
    reg [2:0] DSize, ISize;
    assign DSize = b1.DSize;
    assign ISize = b1.ISize;

    reg Load, Store, Fetch;
    assign Load  = b1.Drd;
    assign Store = b1.Dwr;
    assign Fetch = b1.Ird;
    
    initial begin
        b1.Clk = 0;
        forever begin
            #10 b1.Clk <= ~b1.Clk;
        end
    end

endmodule
