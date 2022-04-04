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
 
interface RVVI_memory;

    reg [31:0] mem [bit[29:0]];

endinterface

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
    RVVI_bus bus   
);

    Uns32 daddr4, iaddr4;
    Uns32 value;
    bit isROM, isRAM;
    Uns32 loROM, hiROM;
    Uns32 loRAM, hiRAM;

    RVVI_memory memory();

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
    
    always @(posedge bus.Clk) begin
        isROM = (bus.IAddr>=loROM && bus.IAddr<=hiROM);
        isRAM = (bus.DAddr>=loRAM && bus.DAddr<=hiRAM);
        
        daddr4 = bus.DAddr >> 2;
        iaddr4 = bus.IAddr >> 2;
        
        // Uninitialized Memory
        if (!memory.mem.exists(daddr4)) memory.mem[daddr4] = 'h0;
        if (!memory.mem.exists(iaddr4)) memory.mem[iaddr4] = 'h0;

        // READ (ROM & RAM)
        if (isROM || isRAM) begin
            if (bus.Drd==1) begin
                bus.DData = memory.mem[daddr4] & byte2bit(bus.Dbe);
                //$display("Load  %08x <= [%08X]", bus.DData, daddr4);
            end
        end

        // WRITE
        if (isRAM) begin
            if (bus.Dwr==1) begin
                value = memory.mem[daddr4] & ~(byte2bit(bus.Dbe));
                memory.mem[daddr4] = value | (bus.DData & byte2bit(bus.Dbe));
                //$display("Store %08x <= %08X", daddr4, mem[daddr4]);
                
            end
        end
        
        // EXEC
        if (isROM) begin
            if (bus.Ird==1) begin
                bus.IData = memory.mem[iaddr4] & byte2bit(bus.Ibe);
                //$display("Fetch %08x <= [%08X]", bus.IData, iaddr4);
            end
        end
        
        // checkers
        if (bus.Ird==1 && isROM==0) begin
            //$display("ERROR: Fetch Address %08X does not have EXECUTE permission", bus.IAddr);
            //$finish;
        end
        if (bus.Drd==1 && isROM==0 && isRAM==0) begin
            //$display("ERROR: Load Address %08X does not have READ permission", bus.DAddr);
            //$finish;
        end
        if (bus.Dwr==1 && isRAM==0) begin
            //$display("ERROR: Store Address %08X does not have WRITE permission", bus.DAddr);
            //$finish;
        end

    end
endmodule
