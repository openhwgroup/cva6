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
#define CUS_ADD(rs1,rs2,rs3,rd) .word 0b##0000000##rs2####rs1##000##rd##0101011
#define CUS_ADD_RS3(rs1,rs2,rs3,rd) .word 0b##rs3##00##rs2####rs1##000##rd##1011011
#define CUS_ADD_MULTI(rs1,rs2,rs3,rd) .word 0b##0000001##rs2####rs1##000##rd##0101011
