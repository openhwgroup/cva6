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


# CUS_ADD rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x0, rd, rs1, rs2
.macro  cus_add rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x0, \rd, \rs1, \rs2
.endm

# CUS_NOP -> .insn r CUSTOM_3, 0x0, 0x0, x0, x0, x0
.macro  cus_nop
    .insn r CUSTOM_3, 0x0, 0x0, x0, x0, x0
.endm

# CUS_NOP_EXC -> .insn r CUSTOM_3, 0x0, 0x20, x0, x0, x0
.macro  cus_nop_exc
    .insn r CUSTOM_3, 0x0, 0x20, x0, x0, x0
.endm

# CUS_ADD_RS3 rd, rs1, rs2, rs3 -> .insn r CUSTOM_3, 0x0, 0x1, rd, rs1, rs2, rs3
.macro  cus_add_rs3 rd, rs1, rs2, rs3
    .insn r CUSTOM_3, 0x0, 0x1, \rd, \rs1, \rs2, \rs3
.endm

# CUS_M_ADD rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x6, rd, rs1, rs2
.macro  cus_m_add rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x6, \rd, \rs1, \rs2
.endm

# CUS_S_ADD rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x2, rd, rs1, rs2
.macro  cus_s_add rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x2, \rd, \rs1, \rs2
.endm

# CUS_ADD_MULTI rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x8, rd, rs1, rs2
.macro  cus_add_multi rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x8, \rd, \rs1, \rs2
.endm

# CUS_EXC rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x40, rd, rs1, rs2
.macro  cus_exc rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x40, \rd, \rs1, \rs2
.endm

# CUS_ISS_EXC rd, rs1, rs2 -> .insn r CUSTOM_3, 0x0, 0x60, rd, rs1, rs2
.macro  cus_iss_exc rd, rs1, rs2
    .insn r CUSTOM_3, 0x0, 0x60, \rd, \rs1, \rs2
.endm

# CUS_LD rd, rs1, simm12 -> .insn i CUSTOM_3, 0x1, rd, rs1, simm12
.macro  cus_ld rd, rs1, simm12
    .insn i CUSTOM_3, 0x1, \rd, \rs1, \simm12
.endm

# CUS_SD rs2, simm12(rs1) -> .insn s CUSTOM_3, 0x2, rs2, simm12(rs1)
.macro  cus_sd rs2, addr
    .insn s CUSTOM_3, 0x2, \rs2, \addr
.endm
