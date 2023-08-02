# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# ------------------------------------------------------------------------------ #

# Add user macros, routines in this file

# Mappings of custom_* mnemonics to .insn pseudo-op of GAS


# CUS_ADD rd, rs1, rs2 -> .insn r CUSTOM_3, 0x1, 0x0, rd, rs1, rs2
.macro  cus_add rd, rs1, rs2
    .insn r CUSTOM_3, 0x1, 0x0, \rd, \rs1, \rs2
.endm

# CUS_NOP -> .insn r CUSTOM_3, 0x0, 0x0, x0, x0, x0
.macro  cus_nop
    .insn r CUSTOM_3, 0x0, 0x0, x0, x0, x0
.endm

# CUS_ADD_RS3 rd, rs1, rs2, rs3 -> .insn r CUSTOM_3, 0x0, 0x1, rd, rs1, rs2, rs3
.macro  cus_add_rs3 rd, rs1, rs2, rs3
    .insn r CUSTOM_3, 0x0, 0x1, \rd, \rs1, \rs2, \rs3
.endm

# CUS_U_ADD rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x2, rd, rs1, rs2
.macro  cus_u_add rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x2, \rd, \rs1, \rs2
.endm

# CUS_S_ADD rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x6, rd, rs1, rs2
.macro  cus_s_add rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x6, \rd, \rs1, \rs2
.endm

# CUS_ADD_MULTI rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x8, rd, rs1, rs2
.macro  cus_add_multi rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x8, \rd, \rs1, \rs2
.endm

# CUS_EXC rs1 -> .insn r CUSTOM_3, 0x2, 0x60, x0, rs1, x0
.macro  cus_exc rs1
    .insn r CUSTOM_3, 0x2, 0x60, x0, \rs1, x0
.endm

