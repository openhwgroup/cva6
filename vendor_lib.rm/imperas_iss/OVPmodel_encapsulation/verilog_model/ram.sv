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

 
`include "typedefs.sv"


module RAM 
(
    BUS SysBus
);
`ifdef DSIM
    reg [31:0] mem [bit [29:0] ]; /* sparse */
`else
    reg /*sparse*/ [31:0] mem ['h00000000:'h3FFFFFFF]; /* sparse */ 
`endif
    Uns32 idx;
    Uns32 value;
    
    function automatic Uns32 byte2bit (input int ByteEn);
        Uns32 BitEn = 0;
        if (ByteEn & 'h1) BitEn |= 'h000000FF;
        if (ByteEn & 'h2) BitEn |= 'h0000FF00;
        if (ByteEn & 'h4) BitEn |= 'h00FF0000;
        if (ByteEn & 'h8) BitEn |= 'hFF000000;
        return BitEn;
    endfunction
    
    always @(posedge SysBus.Clk) begin
        idx = SysBus.Addr >> 2;
        if (SysBus.Transfer==Store) begin
`ifdef DSIM
        if (!mem.exists(idx))
            mem[idx] = 'h0;
`endif
            value = mem[idx] & ~(byte2bit(SysBus.Dbe));
            mem[idx] = value | (SysBus.Data & byte2bit(SysBus.Dbe));
        end else begin
`ifdef DSIM
        if (!mem.exists(idx))
            mem[idx] = 'h0;
`endif
            SysBus.Data = mem[idx] & byte2bit(SysBus.Dbe);
        end
    end
endmodule
