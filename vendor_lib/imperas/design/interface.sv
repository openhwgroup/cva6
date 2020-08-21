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

`ifndef __INCL_INTERFACE_SV
`define __INCL_INTERFACE_SV

//
// Interface definition
//
interface BUS;
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
    
    bit            reset;
    bit            deferint;
    
    bit     [31:0] irq_i;     // Active high level sensitive interrupt inputs
    bit            irq_ack_o; // Interrupt acknowledge
    bit     [4:0]  irq_id_o;  // Interrupt index for taken interrupt - only valid on irq_ack_o = 1
    
    bit            haltreq;
    bit            resethaltreq;
    bit            DM;
    
    //
    // Bus helpers
    //
    bit Shutdown;
    bit Step, Stepping;
    
    //
    // Bus direct transactors
    //
    function automatic int read(input int address);
        if (!ram.mem.exists(address)) ram.mem[address] = 'h0;
        return ram.mem[address];
    endfunction
    function automatic void write(input int address, input int data);
        ram.mem[address] = data;
    endfunction
    
endinterface

`endif
