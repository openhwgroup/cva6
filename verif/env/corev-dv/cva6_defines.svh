// Copyright 2022 Thales DIS design services SAS
// Copyright 2022 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)
// -------------------------------------------------------------------------------------------

// Custom extension instruction for CVXIF
`define DEFINE_CVXIF_CUSTOM_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
   class riscv_``instr_n``_instr extends cvxif_custom_instr;  \
      `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// Zicond extension instruction
`define DEFINE_ZICOND_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
   class riscv_``instr_n``_instr extends riscv_zicond_instr_c;  \
      `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// Zcb extension instruction
`define DEFINE_ZCB_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
   class riscv_``instr_n``_instr extends riscv_zcb_instr_c;  \
      `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// Zcmp extension instruction
`define DEFINE_ZCMP_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
   class riscv_``instr_n``_instr extends riscv_zcmp_instr_c;  \
      `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)
