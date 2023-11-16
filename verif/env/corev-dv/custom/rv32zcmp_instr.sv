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

`DEFINE_ZCMP_INSTR(CM_PUSH,     R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCMP_INSTR(CM_POP,      R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCMP_INSTR(CM_POPRET,   R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCMP_INSTR(CM_POPRETZ,  R_FORMAT,  ARITHMETIC, RV32X)
`DEFINE_ZCMP_INSTR(CM_MVA01S,   R_FORMAT,  LOGICAL, RV32X)
`DEFINE_ZCMP_INSTR(CM_MVSA01,   R_FORMAT,  LOGICAL, RV32X)
