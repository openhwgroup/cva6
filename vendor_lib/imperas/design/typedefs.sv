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

`ifndef __INCL_TYPEDEFS_SV
`define __INCL_TYPEDEFS_SV

typedef byte     Int8;
typedef shortint Int16;
typedef int      Int32;
typedef longint  Int64;
typedef byte     unsigned Uns8;
typedef shortint unsigned Uns16;
typedef int      unsigned Uns32;
typedef longint  unsigned Uns64;

//
// Address label monitor type
//
typedef struct {
    int addr;
    int enable;
} watchT;

`endif