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

`ifndef __INCL_INTERFACE_SV
`define __INCL_INTERFACE_SV

//
// Interface definition
//
interface BUS;
    bit     Clk;
    bit     [31:0] Addr;    // 32-bit Address
    bit     [31:0] Data;    // 32-bit Data
    bit     [3:0]  Dbe;     // Data Lane enables (byte format)
    bit     [2:0]  Size;    // Size of transfer 1-4 bytes
    
    xferE   Transfer;       // Fetch, Load, Store

    bit     reset;
    bit     nmi;
    bit     MSWInterrupt;
    bit     USWInterrupt;
    bit     SSWInterrupt;
    bit     MTimerInterrupt;
    bit     UTimerInterrupt;
    bit     STimerInterrupt;
    bit     MExternalInterrupt;
    bit     UExternalInterrupt;
    bit     SExternalInterrupt;
    
    //
    // Bus helpers
    //
    bit Shutdown;
endinterface

`endif
