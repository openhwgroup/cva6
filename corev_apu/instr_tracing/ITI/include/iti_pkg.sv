// Copyright (c) 2025 Thales DIS design services SAS
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Author: Maxime Colson - Thales
// Date: 20/03/2025
// Contributors: 
// Darshak Sheladiya, SYSGO GmbH
// Umberto Laghi, UNIBO

// This package is temporary, the idea is to have it directly in the encoder later

package iti_pkg;

  localparam CAUSE_LEN = 5;  //Size is ecause_width_p in the E-Trace SPEC
  localparam ITYPE_LEN = 3;  //Size is itype_width_p in the E-Trace SPEC (3 or 4)
  localparam IRETIRE_LEN = 32;  //Size is iretire_width_p in the E-Trace SPEC

  typedef enum logic [ITYPE_LEN-1:0] {
    STANDARD = 0,  // none of the other named itype codes
    EXC = 1,  // exception
    INT = 2,  // interrupt
    ERET = 3,  // exception or interrupt return
    NON_TAKEN_BR = 4,  // nontaken branch
    TAKEN_BR = 5,  // taken branch
    UNINF_JMP = 6,  // uninferable jump if ITYPE_LEN == 3, otherwise reserved
    RES = 7  /*, // reserved
    UC = 8, // uninferable call
    IC = 9, // inferable call
    UIJ = 10, // uninferable jump
    IJ = 11, // inferable jump
    CRS = 12, // co-routine swap
    RET = 13, // return
    OUIJ = 14, // other uninferable jump
    OIJ = 15*/  // other inferable jump
  } itype_t;

endpackage
