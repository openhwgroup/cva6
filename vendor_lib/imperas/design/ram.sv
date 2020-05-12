/*
 *
 * Copyright (c) 2005-2020 Imperas Software Ltd., All Rights Reserved.
 *
 * THIS SOFTWARE CONTAINS CONFIDENTIAL INFORMATION AND TRADE SECRETS
 * OF IMPERAS SOFTWARE LTD. USE, DISCLOSURE, OR REPRODUCTION IS PROHIBITED
 * EXCEPT AS MAY BE PROVIDED FOR IN A WRITTEN AGREEMENT WITH
 * IMPERAS SOFTWARE LTD.
 *
 */
 
 `include "typedefs.sv"

//
// Memory is an array of words
// ROM = ROM_START_ADDR : ROM_START_ADDR+ROM_MEM_DEPTH-1
// RAM = ROM_START_ADDR+ROM_MEM_DEPTH : ROM_START_ADDR+ROM_MEM_DEPTH+RAM_MEM_DEPTH-1
//
module RAM
#(
    parameter int ROM_START_ADDR = 'h8000,
    parameter int ROM_BYTE_SIZE  = 'h20000,
    parameter int RAM_BYTE_SIZE  = 'h20000
)
(
    BUS SysBus
);

    // Sparse memory supported by all RTL simulators
    reg /* sparse */ [31:0] mem [bit[29:0]]; /* sparse */

    Uns32 daddr4, iaddr4;
    Uns32 value;
    bit isROM, isRAM;
    Uns32 loROM, hiROM;
    Uns32 loRAM, hiRAM;
    
    initial begin
        loROM = ROM_START_ADDR;
        hiROM = loROM + ROM_BYTE_SIZE - 1;
        loRAM = hiROM + 1;
        hiRAM = loRAM + RAM_BYTE_SIZE - 1;
    end
    
    function automatic Uns32 byte2bit (input int ByteEn);
        Uns32 BitEn = 0;
        if (ByteEn & 'h1) BitEn |= 'h000000FF;
        if (ByteEn & 'h2) BitEn |= 'h0000FF00;
        if (ByteEn & 'h4) BitEn |= 'h00FF0000;
        if (ByteEn & 'h8) BitEn |= 'hFF000000;
        return BitEn;
    endfunction
    
    always @(posedge SysBus.Clk) begin
        isROM = (SysBus.IAddr>=loROM && SysBus.IAddr<=hiROM);
        isRAM = (SysBus.DAddr>=loRAM && SysBus.DAddr<=hiRAM);
        
        daddr4 = SysBus.DAddr >> 2;
        iaddr4 = SysBus.IAddr >> 2;
        
        // Uninitialized Memory
        if (!mem.exists(daddr4)) mem[daddr4] = 'h0;
        if (!mem.exists(iaddr4)) mem[iaddr4] = 'h0;

        // READ (ROM & RAM)
        if (isROM || isRAM) begin
            if (SysBus.Drd==1) begin
                SysBus.DData = mem[daddr4] & byte2bit(SysBus.Dbe);
                //$display("Load  %08x <= [%08X]", SysBus.DData, daddr4);
            end
        end

        // WRITE
        if (isRAM) begin
            if (SysBus.Dwr==1) begin
                value = mem[daddr4] & ~(byte2bit(SysBus.Dbe));
                mem[daddr4] = value | (SysBus.DData & byte2bit(SysBus.Dbe));
                //$display("Store %08x <= %08X", daddr4, mem[daddr4]);
                
            end
        end
        
        // EXEC
        if (isROM) begin
            if (SysBus.Ird==1) begin
                SysBus.IData = mem[iaddr4] & byte2bit(SysBus.Ibe);
                //$display("Fetch %08x <= [%08X]", SysBus.IData, iaddr4);
            end
        end
        
        // checkers
        if (SysBus.Ird==1 && isROM==0) begin
            //$display("ERROR: Fetch Address %08X does not have EXECUTE permission", SysBus.IAddr);
            //$finish;
        end
        if (SysBus.Drd==1 && isROM==0 && isRAM==0) begin
            //$display("ERROR: Load Address %08X does not have READ permission", SysBus.DAddr);
            //$finish;
        end
        if (SysBus.Dwr==1 && isRAM==0) begin
            //$display("ERROR: Store Address %08X does not have WRITE permission", SysBus.DAddr);
            //$finish;
        end

    end
endmodule
