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
//`define DEBUG
//`define UVM
module CPU 
#(
    parameter int ID = 0
)
(
    BUS SysBus
);

`ifdef UVM
    import uvm_pkg::*;
`endif

    import "DPI-C" context task ovpEntry(input int i, input string s1, input string s2);
    `ifndef UVM
    import "DPI-C" context function void ovpExit(input int);
    `endif

    export "DPI-C" task     busLoad;
    export "DPI-C" task     busStore;
    export "DPI-C" task     busFetch;
    export "DPI-C" task     busWait;
    
    export "DPI-C" function setPC;
    export "DPI-C" function setGPR;
    export "DPI-C" function setFPR;
    export "DPI-C" function setCSR;
    export "DPI-C" function setDECODE;
    export "DPI-C" function getState;
    export "DPI-C" function putState;
    export "DPI-C" task     setRETIRE;
    
    bit [31:0] PC, PCr;
    bit [31:0] GPR[32];
    bit [31:0] FPR[32];
    // ToDo Vector
    bit [31:0] CSR[string];
    
    string Decode, Change;
    bit    [0:(64*8)-1] DecodeP;
    int    Icount = 0;
    event  Retire;
    
    bit mode_disass = 0;
    
    task busStep;
        if (SysBus.Stepping) begin
            while (SysBus.Step == 0) begin
                @(posedge SysBus.Clk);
            end
        end
    endtask
    
    task busWait;
        @(posedge SysBus.Clk);
        busStep;
    endtask
    
    // Called at end of instruction transaction
    task setRETIRE;
        input int retPC;
    
        PCr = retPC;
        Icount++;
        if (mode_disass == 1) begin
            `ifndef UVM
            $display;
            `endif
            if (Icount==0)
                `ifdef UVM
                `uvm_info("riscv_CV32E40P", $sformatf("[%0d] Initial State : %s", ID, Change), UVM_DEBUG)
                `else
                $display("[%0d] Initial State : %s", ID, Change);
                `endif
            else
                `ifdef UVM
                `uvm_info("riscv_CV32E40P", $sformatf("I [%0d] %0d PCr=0x%x %s : %s", ID, Icount, PCr, Decode, Change), UVM_DEBUG)
                `else
                $display("I [%0d] %0d PCr=0x%x %s : %s", ID, Icount, PCr, Decode, Change);
                `endif
        end
        Change = "";
        SysBus.Step = 0;
        ->Retire;
    endtask
    
    function automatic void setPC (input longint value);
        PC = value;
    endfunction
    
    function automatic void putState (
            input int _irq_ack_o,
            input int _irq_id_o,
            input int _DM);
        
        SysBus.irq_ack_o    = _irq_ack_o;
        SysBus.irq_id_o     = _irq_id_o;
        SysBus.DM           = _DM;
    endfunction
        
    function automatic void getState (
            output int _terminate,
            output int _reset,
            output int _deferint,
            output int _irq_i,
            output int _haltreq,
            output int _resethaltreq);
        
        _terminate          = SysBus.Shutdown;
        _reset              = SysBus.reset;
        _deferint           = SysBus.deferint;
        _irq_i              = SysBus.irq_i;
        _haltreq            = SysBus.haltreq ;
        _resethaltreq       = SysBus.resethaltreq ;
    endfunction
        
    function automatic void setDECODE (input string value);
        Decode = value;
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
        `ifdef DEBUG
        `ifdef UVM
        `uvm_info("riscv_CV32E40P", $sformatf("setCSR %16s %x %0t", index, value, $time), UVM_DEBUG)
        `else
        $display("setCSR %16s %x %0t", index, value, $time);
        `endif
        `endif
        CSR[index] = value;
        if (mode_disass == 1) begin
            string ch;
            $sformat(ch, "\n  R CSR[%s]=0x%X", index, value);
            Change = {Change, ch};
        end
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
                    1: enable = 'b0110;
                    2: enable = 'b1100;
                endcase
            end
            3: begin
                case (addr3)
                    0: enable = 'b0111;
                    1: enable = 'b1110;
                endcase
            end
            4: begin
                case (addr3)
                    0: enable = 'b1111;
                endcase
            end
        endcase

        if (enable == 0) begin
            `ifdef UVM
            `uvm_error("riscv_CV32E40P", $sformatf("Data Misaligned address=0x%x size=%0d", address, size))
            `else
            $display("Data Misaligned address=0x%x size=%0d", address, size);
            $finish(-1);
            `endif
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
        
        `ifdef DEBUG
        `ifdef UVM
        `uvm_info("riscv_CV32E40P", $sformatf("%08X = %02x", address, data), UVM_DEBUG);
        `else
        $display("%m %08X = %02x", address, data);
        `endif
        `endif
        wValue = SysBus.read(idx) & ~(byte2bit(ble));
        wValue |= (dValue & byte2bit(ble));
        
        SysBus.write(idx, wValue);
    endfunction
    
    task busStore32;
        input int address;
        input int size;
        input int data;
        input int artifact;
        
        automatic Uns32 ble    = getBLE(address, size);
        automatic Uns32 dValue = getData(address, data);

        if (artifact) begin
            `ifdef DEBUG
            `ifdef UVM
            `uvm_info("riscv_CV32E40P", $sformatf("[%x]<=(%0d)%x ELF_LOAD", address, size, dValue), UVM_DEBUG)
            `else
            $display("%m [%x]<=(%0d)%x ELF_LOAD", address, size, dValue);
            `endif
            `endif
            dmiWrite(address, size, data);

        end else begin
            `ifdef DEBUG
            `ifdef UVM
            `uvm_info("riscv_CV32E40P", $sformatf("[%x]<=(%0d)%x Store", address, size, dValue), UVM_DEBUG)
            `else
            $display("%m [%x]<=(%0d)%x Store", address, size, dValue);
            `endif
            `endif
            SysBus.DAddr  <= address;
            SysBus.DSize  <= size;
            SysBus.Dwr    <= 1;
            SysBus.Dbe    <= ble;
            SysBus.DData  <= dValue;
            
            // wait for the transfer to complete
            busWait;
            SysBus.Dwr    <= 0;
        end
    endtask
     
    task busStore;
        input int address;
        input int size;
        input int data;
        input int artifact;
        
        //
        // Are we over an address boundary ?
        // firstly consider 32 bit
        //
        int overflow;
        overflow = (address & 'h3) + (size - 1);
        
        // Aligned access
        if (overflow < 4) begin
            busStore32(address, size, data, artifact);
        
        // Misaligned access
        end else begin
            int lo, hi, address_lo, address_hi, size_lo, size_hi;
            
            // generate a data for 2 transactions
            lo = data;
            hi = data >> (32 - ((address & 'h3) * 8));
            
            // size_lo number of bytes written to lower word
            size_lo = 4 - (address & 'h3);
            size_hi = size - size_lo;
            
            address_lo = address;
            address_hi = (address & ~('h3)) + 4;
             
            busStore32(address_lo, size_lo, lo, artifact);
            busStore32(address_hi, size_hi, hi, artifact);
        end

    endtask

    function automatic void dmiRead(input int address, input int size, output int data);
        Uns32 rValue;
        Uns32 idx = address >> 2;
        Uns32 ble = getBLE(address, size);
        
        rValue = SysBus.read(idx) & byte2bit(ble);
        
        data = setData(address, rValue);
    endfunction

    task busLoad32;
        input  int address;
        input  int size;
        output int data; 
        input  int artifact; 
        input  int ifetch;

        automatic Uns32 ble = getBLE(address, size);
        
        if (artifact) begin
            dmiRead(address, size, data);

        end else begin
            SysBus.DAddr <= address;
            SysBus.DSize <= size;
            SysBus.Dbe   <= ble;
            SysBus.Drd   <= 1;
            
            // Wait for the transfer to complete & stepping
            busWait;
            data = setData(address, SysBus.DData);
            SysBus.Drd   <= 0;
            
            `ifdef DEBUG
            `ifdef UVM
            `uvm_info("riscv_CV32E40P", $sformatf("[%x]=>(%0d)%x Load", address, size, data), UVM_DEBUG)
            `else
            $display("%m [%x]=>(%0d)%x Load", address, size, data);
            `endif
            `endif
        end
    endtask
    
    task busLoad;
        input  int address;
        input  int size;
        output int data; 
        input  int artifact; 

        //
        // Are we over an address boundary ?
        // firstly consider 32 bit
        //
        int overflow;
        overflow = (address & 'h3) + (size - 1);
        
        // Aligned access
        if (overflow < 4) begin
            busLoad32(address, size, data, artifact, 0);
        
        // Misaligned access
        end else begin
            int lo, hi, address_lo, address_hi;
            
            // generate a wide data value
            address_lo = address & ~('h3);
            address_hi = address_lo + 4;
            busLoad32(address_lo, 4, lo, artifact, 0);
            busLoad32(address_hi, 4, hi, artifact, 0);
        
            data = {hi, lo} >> ((address & 'h3) * 8);
        end
    endtask

    task busFetch32;
        input  int address;
        input  int size;
        output int data; 
        input  int artifact; 

        automatic Uns32 ble = getBLE(address, size);
        
        if (artifact) begin
            dmiRead(address, size, data);

        end else begin
            busStep;
            SysBus.IAddr <= address;
            SysBus.ISize <= size;
            SysBus.Ibe   <= ble;
            SysBus.Ird   <= 1;
            
            setFetchDECODE;
            
            // Wait for the transfer to complete & stepping
            busWait;
            data = setData(address, SysBus.IData);
            SysBus.Ird   <= 0;
            
            `ifdef DEBUG
            `ifdef UVM
            `uvm_info("riscv_CV32E40P", $sformatf("[%x]=>(%0d)%x Fetch", address, size, data), UVM_DEBUG)
            `else
                $display("%m [%x]=>(%0d)%x Fetch", address, size, data);
            `endif
            `endif
        end
    endtask
    
    task busFetch;
        input  int address;
        input  int size;
        output int data; 
        input  int artifact; 

        //
        // Are we over an address boundary ?
        // firstly consider 32 bit
        //
        int overflow;
        overflow = (address & 'h3) + (size - 1);
        
        // Aligned access
        if (overflow < 4) begin
        busFetch32(address, size, data, artifact);
        
        // Misaligned access
        end else begin
            int lo, hi, address_lo, address_hi;
            
            // generate a wide data value
            address_lo = address & ~('h3);
            address_hi = address_lo + 4;
            busFetch32(address_lo, 4, lo, artifact);
            busFetch32(address_hi, 4, hi, artifact);
        
            data = {hi, lo} >> ((address & 'h3) * 8);
        end
    endtask

    function automatic void cpu_cfg();
        if ($test$plusargs("disass"))
            mode_disass = 1;
    endfunction

    string elf_file;
    function automatic void elf_load();
        if (!($value$plusargs("elf_file=%s", elf_file))) begin
            `ifdef UVM
            `uvm_fatal("riscv_CV32E40P", $sformatf("+elf_file=<elf filename> is required"))
            `else
            $display("FATAL: +elf_file=<elf filename> is required");
            $fatal;
            `endif
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
        ovpEntry(ID, ovpcfg, elf_file);
        `ifndef UVM
        $finish;
        `endif
    end
    
    `ifndef UVM
    final begin
        ovpExit(ID);
    end
    `endif
 
endmodule
