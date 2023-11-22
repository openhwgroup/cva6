// Copyright 2022 Thales DIS design services SAS
// Copyright 2022 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)
// ------------------------------------------------------------------------------ //

// Add custom instruction name enum
CUSTOM_1,

//Custom instruction for CVXIF
CUS_ADD,
CUS_ADD_MULTI,
CUS_NOP,
CUS_ADD_RS3,
CUS_EXC,
CUS_U_ADD,
CUS_S_ADD,

//Zicond extension
CZERO_EQZ,
CZERO_NEZ,

//Zcb extension
C_LBU,
C_LH,
C_LHU,
C_SB,
C_SH,
C_MUL,
C_ZEXT_B,
C_SEXT_B,
C_ZEXT_H,
C_SEXT_H,
C_ZEXT_W,
C_NOT,

//Zcmp extension
CM_PUSH,
CM_POP,
CM_POPRET,
CM_POPRETZ,
CM_MVA01S,
CM_MVSA01,
