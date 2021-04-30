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
    reg [31:0] mem [bit[29:0]];
    
    reg [31:0] TICKS;
    reg [31:0] RND_NUM;
    reg [31:0] RND_STALL;

    Uns32 daddr4, iaddr4;
    Uns32 value;
    bit   isROM, isRAM, isIO, isDBG;
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
        //
        // MEM  0x0000_0000 +0x0400_0000
        // IO   0x1000_0000
        // IO   0x1500_0000 +8
        // IO   0x1500_1000 +8
        // IO   0x1600_1000 +0x0010_0000
        // DBG  0x1A11_0800 +0x0000_1000
        // IO   0x2000_1000 +16
        //
        
        isROM = (SysBus.IAddr>=loROM && SysBus.IAddr<=hiROM);
        isRAM = (SysBus.DAddr>=loRAM && SysBus.DAddr<=hiRAM);
        
        isIO  = (SysBus.DAddr>='h10000000 && SysBus.DAddr<='h20000010);
        
        daddr4 = SysBus.DAddr >> 2;
        iaddr4 = SysBus.IAddr >> 2;

        // Uninitialized Memory
        if (!mem.exists(daddr4)) mem[daddr4] = 'h0;
        if (!mem.exists(iaddr4)) mem[iaddr4] = 'h0;

        // READ (ROM & RAM)
        if (isROM || isRAM) begin
            if (SysBus.Drd==1) begin
                SysBus.DData = mem[daddr4] & byte2bit(SysBus.Dbe);
            end
        end
        if (SysBus.Drd == 1 && SysBus.DAddr==32'h1500_1000) begin
            SysBus.DData = dut_wrap.data_rdata;
        end

        // WRITE
        if (isRAM) begin
            if (SysBus.Dwr==1) begin
                value = mem[daddr4] & ~(byte2bit(SysBus.Dbe));
                mem[daddr4] = value | (SysBus.DData & byte2bit(SysBus.Dbe));
            end
        end
        
        // EXEC
        if (isROM) begin
            if (SysBus.Ird==1) begin
                SysBus.IData = mem[iaddr4] & byte2bit(SysBus.Ibe);
            end
        end
        
        if (isIO) begin
            if (SysBus.Dwr==1) begin
                if (SysBus.DAddr == 'h10000000) begin 
                    // $display("IOWR [%08X]<=%08X : Printer", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15000000) begin 
                    // $display("IOWR [%08X]<=%08X : timer_irg_mask", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15000004) begin 
                    // $display("IOWR [%08X]<=%08X : Interrupt Timer Control", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15000008) begin 
                    // $display("IOWR [%08X]<=%08X : Debug Control", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15001000) begin 
                    // $display("IOWR [%08X]<=%08X : Random Number Generator", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15001004) begin 
                    $display("IOWR [%08X]<=%08X : Timer", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h20000000) begin 
                    // $display("IOWR [%08X]<=%08X : Status Flags, Assert", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h20000004) begin 
                    // $display("IOWR [%08X]<=%08X : Status Flags, Assert", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h20000008) begin 
                    // $display("IOWR [%08X]<=%08X : Status Flags, Signature Start", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h2000000C) begin 
                    // $display("IOWR [%08X]<=%08X : Status Flags, Signature End", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h20000010) begin 
                    // $display("IOWR [%08X]<=%08X : Status Flags, Signature Write", SysBus.DAddr, SysBus.DData);
                end else if ((SysBus.DAddr>>16) == 'h1600) begin 
                    // $display("IOWR [%08X]<=%08X : Stall Control", SysBus.DAddr, SysBus.DData);
                end else begin
                    //$display("Error IOWR [%08X]<=%08X : Unknown", SysBus.DAddr, SysBus.DData);
                    //$finish;
                end
            end
            if (SysBus.Drd==1) begin
                if (SysBus.DAddr == 'h10000000) begin 
                    // $display("IORD [%08X]=>%08X : Printer", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15000000) begin 
                    // $display("IORD [%08X]=>%08X : timer_irg_mask", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15000004) begin 
                    // $display("IORD [%08X]=>%08X : Interrupt Timer Control", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15000008) begin 
                    // $display("IORD [%08X]=>%08X : Debug Control", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15001000) begin 
                    SysBus.DData = RND_NUM;
                    // $display("IORD [%08X]=>%08X : Random Number Generator", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h15001004) begin 
                    SysBus.DData = TICKS;
                    // $display("%m IORD [%08X]=>%08X : Timer", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h20000000) begin 
                    // $display("IORD [%08X]=>%08X : Status Flags, Assert", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h20000004) begin 
                    // $display("IORD [%08X]=>%08X : Status Flags, Assert", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h20000008) begin 
                    // $display("IORD [%08X]=>%08X : Status Flags, Signature Start", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h2000000C) begin 
                    // $display("IORD [%08X]=>%08X : Status Flags, Signature End", SysBus.DAddr, SysBus.DData);
                end else if (SysBus.DAddr == 'h20000010) begin 
                    // $display("IORD [%08X]=>%08X : Status Flags, Signature Write", SysBus.DAddr, SysBus.DData);
                end else if ((SysBus.DAddr>>16) == 'h1600) begin 
                    SysBus.DData = RND_STALL;
                    // $display("IORD [%08X]=>%08X : Stall Control", SysBus.DAddr, SysBus.DData);
                end else begin
                    //$display("Error IORD [%08X]=>%08X : Unknown", SysBus.DAddr, SysBus.DData);
                    //$finish;
                end
            end
        end
        
        // checkers
        /*
        if (SysBus.Ird==1 && isROM==0) begin
            $display("ERROR: Fetch Address %08X does not have EXECUTE permission", SysBus.IAddr);
            $finish;
        end
        if (SysBus.Drd==1 && isROM==0 && isRAM==0) begin
            $display("ERROR: Load Address %08X does not have READ permission", SysBus.DAddr);
            $finish;
        end
        if (SysBus.Dwr==1 && isRAM==0) begin
            $display("ERROR: Store Address %08X does not have WRITE permission", SysBus.DAddr);
            $finish;
        end
        */
    end
endmodule
