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

    Uns64 x[32];
    Uns64 f[32];
    Uns64 csr[4096];

    Uns64 count;
    Uns64 trap;

    Uns64 irq_ack_o;
    Uns64 irq_id_o;
    Uns64 DM;

    Uns64 reset;
    Uns64 deferint;
    Uns64 irq_i;
    Uns64 haltreq;
    Uns64 resethaltreq;
    Uns64 cycles;

    Uns64 terminate;
} sharedT;
