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

`DEFINE_CVXIF_CUSTOM_INSTR(CUS_ADD,        R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_CVXIF_CUSTOM_INSTR(CUS_ADD_MULTI,  R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_CVXIF_CUSTOM_INSTR(CUS_NOP,        R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_CVXIF_CUSTOM_INSTR(CUS_ADD_RS3,    R4_FORMAT, ARITHMETIC, RV32X)
`DEFINE_CVXIF_CUSTOM_INSTR(CUS_EXC,        R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_CVXIF_CUSTOM_INSTR(CUS_U_ADD,      R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_CVXIF_CUSTOM_INSTR(CUS_S_ADD,      R_FORMAT,  ARITHMETIC, RV32X)
