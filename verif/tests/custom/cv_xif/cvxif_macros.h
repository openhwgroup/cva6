// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)
// Contributor : Guillaume Chauvon


#define LOAD_RS(rs,value) li rs, value
#define COMP_RS(rs1,rs2,rd) xor rd, rs1, rs2

#define CUS_NOP() .word 0b##0000000##00000####00000##000##00000##1111011
#define CUS_ADD(rs1,rs2,rd) .word 0b##0000000##rs2####rs1##001##rd##1111011
#define CUS_ADD_RS1(rs1,rs2,rd) .word 0b##0000001##rs2####rs1##001##rd##1111011 // only use rs1 : rs1 + rs1 => rd
#define CUS_ADD_RS2(rs1,rs2,rd) .word 0b##0000010##rs2####rs1##001##rd##1111011 // only use rs2 : rs2 + rs2 => rd
#define CUS_ADD_MULTI(rs1,rs2,rd) .word 0b##0000011##rs2####rs1##001##rd##1111011

#define CUS_ADD_RS3_MADD(rs1,rs2,rs3,rd) .word 0b##rs3##00##rs2####rs1##000##rd##1000011 //MADD
#define CUS_ADD_RS3_MSUB(rs1,rs2,rs3,rd) .word 0b##rs3##00##rs2####rs1##000##rd##1000111 //MSUB
#define CUS_ADD_RS3_NMSUB(rs1,rs2,rs3,rd) .word 0b##rs3##00##rs2####rs1##000##rd##1001011 //NMSUB
#define CUS_ADD_RS3_NMADD(rs1,rs2,rs3,rd) .word 0b##rs3##00##rs2####rs1##000##rd##1001111 //NMADD
#define CUS_ADD_RS3_RTYPE(rs1,rs2,rs3) .word 0b##0000100##rs2####rs1##001##rs3##1111011

#define CUS_CADD(rs1, rs2) .half 0b##111##1##rs1##rs2##00 // -> Extend to CUS_ADD(rs1,rs2,x10)
#define CUS_CNOP() .half 0b##111##0##00000##00000##00 // -> Extend to CUS_NOP
