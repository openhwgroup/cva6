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

typedef struct {
    Uns64 retPC;
    Uns64 excPC;
    Uns64 nextPC;

    Uns64 order;
    Uns64 trap;
} RMData_stateT;

typedef struct {
    // Signals to SV
    Uns64 irq_ack_o;
    Uns64 irq_id_o;
    Uns64 sec_lvl_o;
    Uns64 DM;

    // E40X
    Uns64 LR_address;
    Uns64 SC_address;
    Uns64 AMO_active;
} RMData_ioT;


typedef struct {
    // Signals from SV
    Uns64 cycles;
} SVData_stateT;

typedef struct {
    // Signals from SV
    Uns64 reset;
    Uns64 reset_addr;
    Uns64 nmi;
    Uns64 nmi_cause;
    Uns64 nmi_addr;
    Uns64 MSWInterrupt;
    Uns64 MTimerInterrupt;
    Uns64 MExternalInterrupt;
    Uns64 LocalInterrupt0;
    Uns64 LocalInterrupt1;
    Uns64 LocalInterrupt2;
    Uns64 LocalInterrupt3;
    Uns64 LocalInterrupt4;
    Uns64 LocalInterrupt5;
    Uns64 LocalInterrupt6;
    Uns64 LocalInterrupt7;
    Uns64 LocalInterrupt8;
    Uns64 LocalInterrupt9;
    Uns64 LocalInterrupt10;
    Uns64 LocalInterrupt11;
    Uns64 LocalInterrupt12;
    Uns64 LocalInterrupt13;
    Uns64 LocalInterrupt14;
    Uns64 LocalInterrupt15;

    Uns64 deferint;

    Uns64 haltreq;
    Uns64 resethaltreq;

    // E40X
    Uns64 SC_valid;
    Uns64 LoadBusFaultNMI;
    Uns64 StoreBusFaultNMI;
    Uns64 InstructionBusFault;
} SVData_ioT;
