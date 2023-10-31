// Copyright 2023 Thales DIS
// Copyright 2022 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)
// ------------------------------------------------------------------------------ //

`DEFINE_ZCB_INSTR(C_LBU,        CL_FORMAT,  LOAD, RV32X, UIMM)
`DEFINE_ZCB_INSTR(C_LH,         CL_FORMAT,  LOAD, RV32X, UIMM)
`DEFINE_ZCB_INSTR(C_LHU,        CL_FORMAT,  LOAD, RV32X, UIMM)
`DEFINE_ZCB_INSTR(C_SB,         CS_FORMAT,  STORE, RV32X, UIMM)
`DEFINE_ZCB_INSTR(C_SH,         CS_FORMAT,  STORE, RV32X, UIMM)
`DEFINE_ZCB_INSTR(C_MUL,        R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCB_INSTR(C_ZEXT_B,     R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCB_INSTR(C_SEXT_B,     R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCB_INSTR(C_ZEXT_H,     R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCB_INSTR(C_SEXT_H,     R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCB_INSTR(C_NOT,        R_FORMAT,  LOGICAL, RV32X)
