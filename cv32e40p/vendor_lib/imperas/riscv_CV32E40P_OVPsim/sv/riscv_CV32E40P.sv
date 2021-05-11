/*
 *
 * Copyright (c) 2005-2021 Imperas Software Ltd., www.imperas.com
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

interface RVVI_state #(
    parameter int ILEN = 32,
    parameter int XLEN = 32
);

    event            notify;
    
    bit              valid; // Retired instruction
    bit              trap;  // Trapped instruction
    bit              halt;  // Halted  instruction
    
    bit              intr;  // Flag first instruction of trap handler
    bit [(XLEN-1):0] order;
    bit [(ILEN-1):0] insn;
    bit [2:0]        isize;
    bit [1:0]        mode;
    bit [1:0]        ixl;
    
    string           decode;

    bit [(XLEN-1):0] pc;
    bit [(XLEN-1):0] pcnext;

    // Registers
    bit [(XLEN-1):0] x[32];
    bit [(XLEN-1):0] f[32];
    bit [(XLEN-1):0] csr[string];
    
endinterface

typedef enum { IDLE, STEPI, STOP, CONT } rvvi_c_e;
interface RVVI_control;

    event     notify;
    
    rvvi_c_e  cmd;
    bit       ssmode;
    
    bit       state_idle;
    bit       state_stepi;
    bit       state_stop;
    bit       state_cont;
    
    initial ssmode = 1;
    
    assign state_idle  = (cmd == IDLE);
    assign state_stepi = (cmd == STEPI);
    assign state_stop  = (cmd == STOP);
    assign state_cont  = (cmd == CONT);
    
    function automatic void idle();
        cmd = IDLE;
        ->notify;
    endfunction 
    function automatic void stepi();
        cmd = STEPI;
        ->notify;
    endfunction    
    function automatic void stop();
        ssmode = 1;
        cmd = STOP;
        ->notify;
    endfunction    
    function automatic void cont();
        ssmode = 0;
        cmd = CONT;
        ->notify;
    endfunction
    
endinterface

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

    import "DPI-C" context task ovpEntry(input string s1, input string s2);
    `ifndef UVM
    import "DPI-C" context function void ovpExit();
    `endif

    export "DPI-C" task     busFetch;
    export "DPI-C" task     busLoad;
    export "DPI-C" task     busStore;
    export "DPI-C" task     busWait;
    
    export "DPI-C" function setGPR;
    export "DPI-C" function getGPR;
    export "DPI-C" function setFPR;
    export "DPI-C" function setCSR;
    export "DPI-C" function getState;
    export "DPI-C" function putState;
    
    export "DPI-C" task     setRETIRE;
    export "DPI-C" task     setTRAP;
    export "DPI-C" function setDECODE;
    
    RVVI_state   state();
    RVVI_control control();
    
    // From RTL
    bit [31:0] GPR_rtl[32];
    bit [31:0] cycles;

/*
    always @state.notify begin
        if (state.valid) begin
            $display("<R> %s", state.decode);
        end else if (state.trap) begin
            $display("<E> %s", state.decode);
        end else begin
            $display("ERROR: %s", state.decode);
        end
    end
    
    always @control.notify begin
        if (control.cmd == IDLE) begin
            $display("<C> idle");
        end else if (control.cmd == STEPI) begin
            $display("<C> stepi");
        end else if (control.cmd == STOP) begin
            $display("<C> stop");
        end else if (control.cmd == CONT) begin
            $display("<C> continue");
        end
    end
*/

    //
    // Format message for UVM/SV environment
    //
    function automatic void msginfo (input string msg);
    `ifdef UVM
        `uvm_info("riscv_CV32E40P", msg, UVM_DEBUG);
    `else
        $display("riscv_CV32E40P: %s", msg);
    `endif
    endfunction
    
    function automatic void msgfatal (input string msg);
    `ifdef UVM
        `uvm_fatal("riscv_CV32E40P", msg);
    `else
        $display("riscv_CV32E40P: %s", msg);
        $fatal;
    `endif
    endfunction
    
    task busStep;
        if (control.ssmode) begin
            while (control.cmd != STEPI) begin
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
        input int hart;
        input int retPC;
        input int nextPC;
        input longint count;
    
        control.idle();
        
        // RVVI_S
        state.trap   = 0; 
        state.valid  = 1;
        state.pc     = retPC;
        state.pcnext = nextPC;
        state.order  = count;
        ->state.notify;
    endtask

    task setTRAP;
        input int hart;
        input int excPC;
        input int nextPC;
        input longint count;
        
        control.idle();
        
        // RVVI_S
        state.trap   = 1; 
        state.valid  = 0;
        state.pc     = excPC;
        state.pcnext = nextPC;
        state.order  = count;
        ->state.notify;
    endtask
        
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
            output int _resethaltreq,
            output int _cycles
            );
        
        _terminate          = SysBus.Shutdown;
        _reset              = SysBus.reset;
        _deferint           = SysBus.deferint;
        _irq_i              = SysBus.irq_i;
        _haltreq            = SysBus.haltreq;
        _resethaltreq       = SysBus.resethaltreq;
        
        _cycles             = cycles;
    endfunction
        
    function automatic void setDECODE (input string value, input int insn, input int isize);
        state.decode = value;
        state.insn   = insn;
        state.isize  = isize;
    endfunction
    
    function automatic void setGPR (input int index, input longint value);
        state.x[index] = value;
    endfunction
    
    function automatic void getGPR (input int index, output longint value);
        value = GPR_rtl[index];
    endfunction
    
    function automatic void setFPR (input int index, input longint value);
        state.f[index] = value;
    endfunction
    
    function automatic void setCSR (input string index, input longint value);
        state.csr[index] = value;
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
            msginfo($sformatf("Data Misaligned address=0x%x size=%0d", address, size));
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
        msginfo($sformatf("%08X = %02x", address, data));
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
            msginfo($sformatf("[%x]<=(%0d)%x ELF_LOAD", address, size, dValue));
            `endif
            dmiWrite(address, size, data);

        end else begin
            `ifdef DEBUG
            msginfo($sformatf("[%x]<=(%0d)%x Store", address, size, dValue));
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
        input  int address;
        input  int size;
        input  int data;
        input  int artifact;
        output int fault; 
        
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
        
        // Determine fault logic
        fault = 0;
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
            
            // Wait for the transfer to complete & ssmode
            busWait;
            data = setData(address, SysBus.DData);
            SysBus.Drd   <= 0;
            
            `ifdef DEBUG
            msginfo($sformatf("[%x]=>(%0d)%x Load", address, size, data));
            `endif
        end
    endtask
    
    task busLoad;
        input  int address;
        input  int size;
        output int data; 
        input  int artifact; 
        output int fault; 

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

        // Determine fault logic
        fault = 0;
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
            
            // Wait for the transfer to complete & ssmode
            busWait;
            data = setData(address, SysBus.IData);
            SysBus.Ird   <= 0;
            
            `ifdef DEBUG
            msginfo($sformatf("[%x]=>(%0d)%x Fetch", address, size, data));
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

    string elf_file;
    function automatic void elf_load();
        if (!($value$plusargs("elf_file=%s", elf_file))) begin
            msgfatal($sformatf("+elf_file=<elf filename> is required"));
        end
    endfunction
    
    string ovpcfg;
    function automatic void ovpcfg_load();
        ovpcfg = "";
        if ($value$plusargs("ovpcfg=%s", ovpcfg)) begin
        end
    endfunction
    
    initial begin
        if ($test$plusargs("USE_ISS")) begin            
            ovpcfg_load();
            elf_load();
            ovpEntry(ovpcfg, elf_file);
            `ifndef UVM
            $finish;
            `endif
        end
    end
    
    `ifndef UVM
    final begin
        ovpExit();
    end
    `endif
 
endmodule
