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

 
`include "interface.sv"
module CPU 
#(
    parameter ID      = 0,
`ifdef DSIM
    parameter string VENDOR  = "riscv.ovpworld.org",
    parameter string VARIANT = "RV32IMC",//"RV32GC",
`else
    parameter VENDOR  = "riscv.ovpworld.org",
    parameter VARIANT = "RV32IMC",//"RV32GC",
`endif
    parameter COMPARE = 0
)
(
    BUS SysBus
);
`ifdef VCS
    import "DPI-C" context task cpu_init (int, string, string, string, string, int);
    import "DPI-C" function int cpu_term (int, string);
`else
    import "DPI-C" context task cpu_init (input int, input string, input string, input string, input string, input int);
    import "DPI-C" function int cpu_term (input int, input string);
`endif

    export "DPI-C" task     busWrite;
    export "DPI-C" task     busRead;
    export "DPI-C" task     busWait;
    
    export "DPI-C" function setPC;
    export "DPI-C" function setGPR;
    export "DPI-C" function setFPR;
    export "DPI-C" function setCSR;
    export "DPI-C" function setDECODE;
    export "DPI-C" function getState;
    export "DPI-C" task     setRETIRE;
    
    bit [63:0] PC, PCr;
    bit [63:0] GPR[32];
    bit [63:0] FPR[32];
    // ToDo Vector
    bit [63:0] CSR[string];
    
    string Decode, Change;
    bit    [0:(64*8)-1] DecodeP;
    int    Icount = 0;
    event  Retire;
    bit    StepEnable, Step;
    
    bit mode_disass = 0;
    bit mode_disass_display = 0;
    
    task busWait;
        //$display("%m entering busWait @ %0t", $time);
        @(posedge SysBus.Clk);
        if (StepEnable) begin
            while (!Step) begin
                @(posedge SysBus.Clk);
            end
        end
        //$display("%m exiting busWait @ %0t", $time);
    endtask
    
    // Called at end of instruction transaction
    task setRETIRE;
        if (mode_disass_display == 1) begin
            if (Icount==0) 
                $display("[%0d] Initial State : %s", ID, Change);
            else
                $display("I [%0d] %0d PCr=0x%x %s : %s", ID, Icount, PCr, Decode, Change);
            Change = "";
        end
        Icount++;
        Step = 0;
        ->Retire;
    endtask
    
    function automatic void getState (
            output int _terminate,
            output int _reset,
            output int _nmi,
            output int _MSWInterrupt,
            output int _USWInterrupt,
            output int _SSWInterrupt,
            output int _MTimerInterrupt,
            output int _UTimerInterrupt,
            output int _STimerInterrupt,
            output int _MExternalInterrupt,
            output int _UExternalInterrupt,
            output int _SExternalInterrupt);

        _terminate          = SysBus.Shutdown;
        _reset              = SysBus.reset;
        _nmi                = SysBus.nmi;
        _MSWInterrupt       = SysBus.MSWInterrupt;
        _USWInterrupt       = SysBus.USWInterrupt;
        _SSWInterrupt       = SysBus.SSWInterrupt;
        _MTimerInterrupt    = SysBus.MTimerInterrupt;
        _UTimerInterrupt    = SysBus.UTimerInterrupt;
        _STimerInterrupt    = SysBus.STimerInterrupt;
        _MExternalInterrupt = SysBus.MExternalInterrupt;
        _UExternalInterrupt = SysBus.UExternalInterrupt;
        _SExternalInterrupt = SysBus.SExternalInterrupt;
    endfunction
        
    function automatic void setDECODE (input string value);
        if (mode_disass == 1) begin
            Decode = value;
        end
    endfunction
    
    function automatic void setFetchDECODE ();
        if (mode_disass == 1) begin
            DecodeP[0:7]     = Decode.getc(0);
            DecodeP[8:15]    = Decode.getc(1);
            DecodeP[16:23]   = Decode.getc(2);
            DecodeP[24:31]   = Decode.getc(3);
            DecodeP[32:39]   = Decode.getc(4);
            DecodeP[40:47]   = Decode.getc(5);
            DecodeP[48:55]   = Decode.getc(6);
            DecodeP[56:63]   = Decode.getc(7);
            DecodeP[64:71]   = Decode.getc(8);
            DecodeP[72:79]   = Decode.getc(9);
            DecodeP[80:87]   = Decode.getc(10);
            DecodeP[88:95]   = Decode.getc(11);
            DecodeP[96:103]  = Decode.getc(12);
            DecodeP[104:111] = Decode.getc(13);
            DecodeP[112:119] = Decode.getc(14);
            DecodeP[120:127] = Decode.getc(15);
            DecodeP[128:135] = Decode.getc(16);
            DecodeP[136:143] = Decode.getc(17);
            DecodeP[144:151] = Decode.getc(18);
            DecodeP[152:159] = Decode.getc(19);
            DecodeP[160:163] = Decode.getc(20);
        end
    endfunction
    
    function automatic void setGPR (input int index, input longint value);
        $display("[%m] @%0t: setGPR 'd%0d 'h%x\n", $time, index, value);
        GPR[index] = value;
        if (mode_disass == 1) begin
            string ch;
            $sformat(ch, "\n  R GPR[%0d]=0x%X", index, value);
            Change = {Change, ch};
        end
    endfunction
    
    function automatic void setFPR (input int index, input longint value);
        FPR[index] = value;
        if (mode_disass == 1) begin
            string ch;
            $sformat(ch, "\n  R FPR[%0d]=0x%X", index, value);
            Change = {Change, ch};
        end
    endfunction
    
    function automatic void setCSR (input string index, input longint value);
        $display("[%m] setCSR %16s %x\n", index, value);
        CSR[index] = value;
        if (mode_disass == 1) begin
            string ch;
            $sformat(ch, "\n  R CSR[%s]=0x%X", index, value);
            Change = {Change, ch};
        end
    endfunction
    
    function automatic void setPC (input longint value);
        //$display("%m (setPC) @ %0t\n", $time);
        PCr = PC;
        PC  = value;
    endfunction
    
    //
    // Byte lane enables based upon size and address
    //
    function automatic Uns32 getBLE (input int address, input int size);
        Uns32 addr3 = address & 3;
        Uns32 enable = 0;
        case (size)
            1: begin
                case (addr3)
                    0: enable = 'b0001;
                    1: enable = 'b0010;
                    2: enable = 'b0100;
                    3: enable = 'b1000;
                endcase
            end
            2: begin
                case (addr3)
                    0: enable = 'b0011;
                    2: enable = 'b1100;
                endcase
            end
            4: begin
                case (addr3)
                    0: enable = 'b1111;
                endcase
            end
        endcase

        if (enable == 0) begin
            $display("[%m][%0d]Data Misaligned address=0x%x size=%0d", ID, address, size);
            $fatal;
        end
        return enable;
    endfunction
    
    function automatic Uns32 byte2bit (input int ByteEn);
        Uns32 BitEn = 0;
        if (ByteEn & 'h1) BitEn |= 'h000000FF;
        if (ByteEn & 'h2) BitEn |= 'h0000FF00;
        if (ByteEn & 'h4) BitEn |= 'h00FF0000;
        if (ByteEn & 'h8) BitEn |= 'hFF000000;
        return BitEn;
    endfunction
    
    // shift data based upon byte address
    function automatic Uns32 getData (input int address, input int data);
        Uns32 addr3 = address & 3;
        Uns32 sdata = data << (addr3 * 8);
        return sdata;
    endfunction
    
    // shift data based upon byte address
    function automatic Uns32 setData (input int address, input int data);
        Uns32 addr3 = address & 3;
        Uns32 sdata = data >> (addr3 * 8);
        return sdata;
    endfunction
    
    function automatic void dmiWrite(input int address, input int size, input int data);
        Uns32 wValue;
        Uns32 idx    = address >> 2;
        Uns32 ble    = getBLE(address, size);
        Uns32 dValue = getData(address, data);
        
`ifdef DSIM
        if (!ram.mem.exists(idx))
            ram.mem[idx] = 'h0;
`endif
        wValue = ram.mem[idx] & ~(byte2bit(ble));
        wValue |= (dValue & byte2bit(ble));
        ram.mem[idx] = wValue;
    endfunction
    
    task busWrite;
        input int address;
        input int size;
        input int data;
        input int artifact;
        
        automatic Uns32 ble    = getBLE(address, size);
        automatic Uns32 dValue = getData(address, data);

        if (artifact) begin
            dmiWrite(address, size, data);

        end else begin
        	`ifdef DEBUG
            $display("%m [%x]<=(%0d)%x Store", address, size, dValue);
            `endif
            SysBus.Addr     <= address;
            SysBus.Size     <= size;
            SysBus.Transfer <= Store;
            SysBus.Dbe      <= ble;
            SysBus.Data     <= dValue;
            
            // wait for the transfer to complete
            busWait;
            SysBus.Transfer <= Null;

        end
    endtask

    function automatic void dmiRead(input int address, input int size, output int data);
        Uns32 rValue;
        Uns32 idx = address >> 2;
        Uns32 ble = getBLE(address, size);
        
        rValue = ram.mem[idx] & byte2bit(ble);
        
        data = setData(address, rValue);
    endfunction

    task busRead;
        input  int address;
        input  int size;
        output int data; 
        input  int artifact; 
        input  int ifetch;

        automatic Uns32 ble = getBLE(address, size);
        
        if (artifact) begin
            if (ifetch) $display("AR FETCH %d %08X", size, address);
            dmiRead(address, size, data);

        end else begin
            if (ifetch) $display("RL FETCH %d %08X", size, address);
            SysBus.Addr <= address;
            SysBus.Size <= size;
            SysBus.Dbe  <= ble;
            if (ifetch) begin
                SysBus.Transfer <= Fetch;
                setFetchDECODE;
            end else begin
                SysBus.Transfer <= Load;
            end
            
            // Wait for the transfer to complete & stepping
            busWait;
            data = setData(address, SysBus.Data);
            SysBus.Transfer <= Null;
            
            `ifdef DEBUG
            if (ifetch) 
                $display("%m [%x]=>(%0d)%x Fetch", address, size, data);
            else
                $display("%m [%x]=>(%0d)%x Load", address, size, data);
            `endif
        end
    endtask

    function automatic void cpu_cfg();
        if ($test$plusargs("disass"))
            mode_disass = 1;
        if ($test$plusargs("disass_display"))
            mode_disass_display = 1;
    endfunction

    string elf_file;
    function automatic void elf_load();
        if (!($value$plusargs("elf_file=%s", elf_file))) begin
            $display("FATAL: +elf_file=<elf filename> is required");
            $fatal;
        end
    endfunction
    
    string ovpcfg;
    function automatic void ovpcfg_load();
        ovpcfg = "";
        if ($value$plusargs("ovpcfg=%s", ovpcfg)) begin
        end
    endfunction
    
    initial begin
        ovpcfg_load();
        elf_load();
        cpu_cfg();
        cpu_init(ID, ovpcfg, VENDOR, VARIANT, elf_file, (mode_disass || COMPARE));
    end

    final begin
        void'(cpu_term(ID, "cpu.sv"));
    end
 
endmodule
