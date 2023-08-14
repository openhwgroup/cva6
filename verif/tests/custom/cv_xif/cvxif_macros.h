// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


#define LOAD_RS(rs,value) li rs, value
#define COMP_RS(rs1,rs2,rd) xor rd, rs1, rs2
#define CUS_ADD(rs1,rs2,rd) .word 0b##0000000##rs2####rs1##001##rd##1111011
#define CUS_NOP(rs1,rs2,rd) .word 0b##0000000##00000####00000##000##00000##1111011
#define CUS_ADD_RS3(rs1,rs2,rs3,rd) .word 0b##rs3##01##rs2####rs1##000##rd##1111011
#define CUS_ADD_MULTI(rs1,rs2,rd) .word 0b##0001000##rs2####rs1##000##rd##1111011
#define CUS_EXC(rs1,rs2,rs3,rd) .word 0b####1100000##rs2####rs1##010##rd##1111011
#define CUS_U_ADD(rs1,rs2,rd) .word 0b####0000010##rs2####rs1##000##rd##1111011
#define CUS_S_ADD(rs1,rs2,rd) .word 0b####0000110##rs2####rs1##000##rd##1111011
