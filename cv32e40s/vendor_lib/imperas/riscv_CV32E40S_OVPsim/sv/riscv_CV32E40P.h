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

    // Signals to SV
    Uns64 irq_ack_o;
    Uns64 irq_id_o;
    Uns64 DM;
} RMDataT;

typedef struct {
    // Signals from SV
    Uns64 reset;
    Uns64 deferint;
    Uns64 irq_i;
    Uns64 haltreq;
    Uns64 resethaltreq;
    Uns64 terminate;

    // E40S
    Uns64 LoadBusFaultNMI;
    Uns64 StoreBusFaultNMI;
    Uns64 InstructionBusFault;

    Uns64 cycles;
} SVDataT;
