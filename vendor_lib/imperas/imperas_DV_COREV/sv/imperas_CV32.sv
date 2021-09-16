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
 
//`define DEBUG
//`define UVM

`include "typedefs.sv"

`include "imperas_CV32.h"

`ifndef DMI_RAM_PATH
  `define DMI_RAM_PATH ram.memory.mem
`endif

interface RVVI_state #(
    parameter int ILEN = 32,
    parameter int XLEN = 32
);
    //
    // RISCV output signals
    //
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
    bit [(XLEN-1):0] c[bit[11:0]];
    bit [(XLEN-1):0] csr[string];
    
    // Temporary hack for volatile CSR reads
    bit [31:0] GPR_rtl[32];
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

interface RVVI_io;
    bit         reset;
    bit  [31:0] reset_addr;
    bit         nmi;
    bit  [31:0] nmi_cause;
    bit  [31:0] nmi_addr;
    
    bit  [31:0] irq_i;     // Active high level sensitive interrupt inputs
    bit         irq_ack_o; // Interrupt acknowledge
    bit  [4:0]  irq_id_o;  // Interrupt index for taken interrupt - only valid on irq_ack_o = 1
    bit         deferint;  // Artifact signal to gate the last stage of interrupt
    
    bit         haltreq;
    bit         resethaltreq;
    bit         DM;
    
    bit         Shutdown;
endinterface

interface RVVI_bus;
    bit     Clk;
    
    bit     [31:0] DAddr;   // Data Bus Address
    bit     [31:0] DData;   // Data Bus LSU Data
    bit     [3:0]  Dbe;     // Data Bus Lane enables (byte format)
    bit     [2:0]  DSize;   // Data Bus Size of transfer 1-4 bytes
    bit            Dwr;     // Data Bus write
    bit            Drd;     // Data Bus read
    
    bit     [31:0] IAddr;   // Instruction Bus Address
    bit     [31:0] IData;   // Instruction Bus Data
    bit     [3:0]  Ibe;     // Instruction Bus Lane enables (byte format)
    bit     [2:0]  ISize;   // Instruction Bus Size of transfer 1-4 bytes
    bit            Ird;     // Instruction Bus read

    bit            LoadBusFaultNMI;     // Artifact to signal memory interface error (E40X)
    bit            StoreBusFaultNMI;    // Artifact to signal memory interface error (E40X)
    bit            InstructionBusFault; // Artifact to signal memory interface error (E40X)

endinterface

module CPU #(
    parameter int ID = 0,
    parameter string VARIANT = "UNSET"
)(
    RVVI_bus bus,
    RVVI_io  io
);

`ifdef UVM
    import uvm_pkg::*;
`endif

    import "DPI-C" context task          svimp_entry(input string s1, input string s2, input string s3);
    import "DPI-C" context function void svimp_pull(output RMDataT RMData);
    import "DPI-C" context function void svimp_push(input  SVDataT SVData);
    import "DPI-C" context function void svimp_exit();

    export "DPI-C" task     svexp_busFetch;
    export "DPI-C" task     svexp_busLoad;
    export "DPI-C" task     svexp_busStore;
    export "DPI-C" task     svexp_busWait;
    
    export "DPI-C" function svexp_setGPR;
    export "DPI-C" function svexp_getGPR;
    
    export "DPI-C" function svexp_setCSR;
    export "DPI-C" function svexp_pull;
    
    export "DPI-C" task     svexp_setRESULT;
    export "DPI-C" function svexp_setDECODE;
    
    RVVI_state   state();
    RVVI_control control();
    
    bit [31:0] cycles;

    RMDataT RMData;
    SVDataT SVData;

    //
    // Bus direct transactors
    //
    function automatic int read(input int address);
        if (!`DMI_RAM_PATH.exists(address)) `DMI_RAM_PATH[address] = 'h0;
        return `DMI_RAM_PATH[address];
    endfunction
    function automatic void write(input int address, input int data);
        `DMI_RAM_PATH[address] = data;
    endfunction

    //
    // Format message for UVM/SV environment
    //
    function automatic void msginfo (input string msg);
    `ifdef DEBUG
        `ifdef UVM
            `uvm_info(VARIANT, msg, UVM_DEBUG);
        `else
            $display("%s: %s", msg, VARIANT);
        `endif
    `endif
    endfunction
    
    function automatic void msgfatal (input string msg);
    `ifdef UVM
        `uvm_fatal(VARIANT, msg);
    `else
        $display("%s: %s", msg, VARIANT);
        $fatal;
    `endif
    endfunction
    
    task busStep;
        if (control.ssmode) begin
            while (control.cmd != STEPI) begin
                @(posedge bus.Clk);
            end
        end
    endtask
    
    task busWait;
        @(posedge bus.Clk);
        busStep;
    endtask
    
    task svexp_busWait;
        busWait;
    endtask
    
    //
    // getState values set by RM
    //
    function automatic void getState;
        int i;
        svimp_pull(RMData);

        io.irq_ack_o = RMData.irq_ack_o;
        io.irq_id_o  = RMData.irq_id_o;
        io.DM        = RMData.DM;
    endfunction
    
    // Called at end of instruction transaction
    task svexp_setRESULT;
        input int isvalid;
        
        control.idle();

        getState();
                
        // RVVI_S
        if (isvalid) begin
            state.valid = 1;
            state.trap  = 0;
            state.pc    = RMData.retPC;
        end else begin
            state.valid = 0;
            state.trap  = 1;
            state.pc    = RMData.excPC;
        end
        
        state.pcnext = RMData.nextPC;
        state.order  = RMData.order;
        
        ->state.notify;
    endtask

    //
    // pack values to be used by RM
    //
    function automatic void svexp_pull;
        SVData.reset               = io.reset;
        SVData.reset_addr          = io.reset_addr;
        SVData.nmi                 = io.nmi;
        SVData.nmi_cause           = io.nmi_cause;
        SVData.nmi_addr            = io.nmi_addr;
        
        SVData.MSWInterrupt        = io.irq_i[3];
        SVData.MTimerInterrupt     = io.irq_i[7];
        SVData.MExternalInterrupt  = io.irq_i[11];
        SVData.LocalInterrupt0     = io.irq_i[16];
        SVData.LocalInterrupt1     = io.irq_i[17];
        SVData.LocalInterrupt2     = io.irq_i[18];
        SVData.LocalInterrupt3     = io.irq_i[19];
        SVData.LocalInterrupt4     = io.irq_i[20];
        SVData.LocalInterrupt5     = io.irq_i[21];
        SVData.LocalInterrupt6     = io.irq_i[22];
        SVData.LocalInterrupt7     = io.irq_i[23];
        SVData.LocalInterrupt8     = io.irq_i[24];
        SVData.LocalInterrupt9     = io.irq_i[25];
        SVData.LocalInterrupt10    = io.irq_i[26];
        SVData.LocalInterrupt11    = io.irq_i[27];
        SVData.LocalInterrupt12    = io.irq_i[28];
        SVData.LocalInterrupt13    = io.irq_i[29];
        SVData.LocalInterrupt14    = io.irq_i[30];
        SVData.LocalInterrupt15    = io.irq_i[31];

        SVData.deferint            = io.deferint;

        SVData.haltreq             = io.haltreq;
        SVData.resethaltreq        = io.resethaltreq;
        
        SVData.LoadBusFaultNMI     = bus.LoadBusFaultNMI;
        SVData.StoreBusFaultNMI    = bus.StoreBusFaultNMI;
        SVData.InstructionBusFault = bus.InstructionBusFault;
        
        
        SVData.cycles              = cycles;
        
        svimp_push(SVData);
    endfunction

    function automatic void svexp_setDECODE (input string value, input int insn, input int isize);
        state.decode = value;
        state.insn   = insn;
        state.isize  = isize;
    endfunction
    
    function automatic void svexp_getGPR (input int index, output longint value);
        value = state.GPR_rtl[index];
    endfunction
    
    function automatic void svexp_setGPR (input int index, input longint value);
        state.x[index] = value;
    endfunction
    
    function automatic void svexp_setCSR (input string name, input int index, input longint value);
        state.csr[name] = value;
        state.c[index]  = value;
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
        Uns32 addr4 = address & 3;
        Uns32 sdata = data << (addr4 * 8);
        return sdata;
    endfunction
    
    // shift data based upon byte address
    function automatic Uns32 setData (input int address, input int data);
        Uns32 addr4 = address & 3;
        Uns32 sdata = data >> (addr4 * 8);
        return sdata;
    endfunction
    
    function automatic void dmiWrite(input int address, input int ble, input int data);
        Uns32 wValue;
        Uns32 idx    = address >> 2;
        Uns32 dValue = getData(address, data);
        
        msginfo($sformatf("%08X = %02x", address, data));
        wValue = read(idx) & ~(byte2bit(ble));
        wValue |= (dValue & byte2bit(ble));
        
        write(idx, wValue);
    endfunction
    
    task busStore32;
        output int fault; 
        input  int address;
        input  int size;
        input  int data;
        input  int artifact;
        
        automatic Uns32 ble    = getBLE(address, size);
        automatic Uns32 dValue = getData(address, data);

        if (artifact) begin
            msginfo($sformatf("[%x]<=(%0d)%x ELF_LOAD", address, size, dValue));
            dmiWrite(address, ble, data);

        end else begin
            msginfo($sformatf("[%x]<=(%0d)%x Store", address, size, dValue));
            bus.DAddr  = address;
            bus.DSize  = size;
            bus.Dwr    = 1;
            bus.Dbe    = ble;
            bus.DData  = dValue;
            
            // wait for the transfer to complete
            busWait;
            bus.Dwr    = 0;
            fault      = bus.StoreBusFaultNMI;
        end
    endtask
     
    task svexp_busStore;
        output int fault; 
        input  int address;
        input  int size;
        input  int data;
        input  int artifact;
        
        //
        // Are we over an address boundary ?
        // firstly consider 32 bit
        //
        int overflow;
        overflow = (address & 'h3) + (size - 1);
        
        // Aligned access
        if (overflow < 4) begin
            busStore32(fault, address, size, data, artifact);
        
        // Misaligned access
        end else begin
            int lo, hi, address_lo, address_hi, size_lo, size_hi, fault_lo, fault_hi;
            
            // generate a data for 2 transactions
            lo = data;
            hi = data >> (32 - ((address & 'h3) * 8));
            
            // size_lo number of bytes written to lower word
            size_lo = 4 - (address & 'h3);
            size_hi = size - size_lo;
            
            address_lo = address;
            address_hi = (address & ~('h3)) + 4;
             
            busStore32(fault_lo, address_lo, size_lo, lo, artifact);
            busStore32(fault_hi, address_hi, size_hi, hi, artifact);
            fault = fault_lo | fault_hi; // TODO
        end
    endtask

    function automatic void dmiRead(input int address, input int ble, output int data);
        Uns32 rValue;
        Uns32 idx = address >> 2;
        
        rValue = read(idx) & byte2bit(ble);
        
        data = setData(address, rValue);
    endfunction

    task busLoad32;
        output int fault;
        input  int address;
        input  int size;
        output int data; 
        input  int artifact; 

        automatic Uns32 ble = getBLE(address, size);
        
        if (artifact) begin
            dmiRead(address, ble, data);

        end else begin
            bus.DAddr = address;
            bus.DSize = size;
            bus.Dbe   = ble;
            bus.Drd   = 1;
            
            // Wait for the transfer to complete & ssmode
            busWait;
            data      = setData(address, bus.DData);
            fault     = bus.LoadBusFaultNMI;
            bus.Drd   = 0;
            
            msginfo($sformatf("[%x]=>(%0d)%x Load", address, size, data));
        end
    endtask
    
    task svexp_busLoad;
        output int fault;
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
            busLoad32(fault, address, size, data, artifact);
        
        // Misaligned access
        end else begin
            int lo, hi, address_lo, address_hi, fault_lo, fault_hi;
            
            // generate a wide data value
            address_lo = address & ~('h3);
            address_hi = address_lo + 4;
            busLoad32(fault_lo, address_lo, 4, lo, artifact);
            busLoad32(fault_hi, address_hi, 4, hi, artifact);
        
            data = {hi, lo} >> ((address & 'h3) * 8);
            fault = fault_lo | fault_hi; // TODO
        end
    endtask

    /* always fetch 32 and cache full word for successive B/HW accesses */
    reg [31:0] cache_waddr;
    reg [31:0] cache_wdata;
    reg        cache_fault;
    task busFetch32;
        output int fault;
        input  int address;
        input  int size;
        output int data; 
        input  int artifact; 

        // word aligned address
        automatic Uns32 waddr = address & ~3;
        automatic Uns32 wdata;
        
        automatic Uns32 ble = getBLE(address, size);
        
        if (artifact) begin
            dmiRead(address, ble, data);

        end else begin
            if ((cache_waddr == waddr) && (cache_fault == 0)) begin
                wdata  = setData(address, cache_wdata);
                fault  = cache_fault;
                
            end else begin
                busStep;
                bus.IAddr = waddr;
                bus.ISize = 4;
                bus.Ibe   = 'hF;
                bus.Ird   = 1;
                
                // Wait for the transfer to complete & ssmode
                busWait;
                
                wdata     = setData(address, bus.IData);
                fault     = bus.InstructionBusFault;
                bus.Ird   = 0;
                
            end
            
            msginfo($sformatf("[%x]=>(%0d)%x Fetch", address, size, data));
            
            // Save for next cached access
            cache_waddr = waddr;
            cache_wdata = wdata;
            cache_fault = fault;
            
            data = wdata & byte2bit(ble);
            
            //$display("busFetch32 address=%08X cache_waddr=%08X : data=%08X cache_wdata=%08X fault=%0d", 
            //    address, cache_waddr, data, cache_wdata, fault);
        end
    endtask
    
    task svexp_busFetch;
        output int fault;
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
            busFetch32(fault, address, size, data, artifact);
        
        // Misaligned access
        end else begin
            int lo, hi, address_lo, address_hi, fault_lo, fault_hi;
            
            // generate a wide data value
            address_lo = address & ~('h3);
            address_hi = address_lo + 4;
            busFetch32(fault_lo, address_lo, 4, lo, artifact);
            busFetch32(fault_hi, address_hi, 4, hi, artifact);
        
            data = {hi, lo} >> ((address & 'h3) * 8);
            fault = fault_lo | fault_hi; // TODO
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
        if (!$test$plusargs("DISABLE_OVPSIM")) begin
            #1;
            ovpcfg_load();
            elf_load();
            svimp_entry(ovpcfg, elf_file, VARIANT);
        `ifndef UVM
            $finish;
        `endif
        end
    end
    
`ifndef UVM
    final begin
        svimp_exit();
    end
`endif
 
endmodule
