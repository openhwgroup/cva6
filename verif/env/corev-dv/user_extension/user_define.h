# Copyright 2023 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# ------------------------------------------------------------------------------ #

# Add user macros, routines in this file

# Mappings of zicond extension mnemonics to .insn pseudo-op of GAS


# CZERO_EQZ rd, rs1, rs2 -> .insn r 0x33, 0x5, 0x7, rd, rs1, rs2
.macro  czero_eqz rd, rs1, rs2
    .insn r 0x33, 0x5, 0x7, \rd, \rs1, \rs2
.endm

# CZERO_NEZ rd, rs1, rs2 -> .insn r 0x33, 0x7, 0x7, rd, rs1, rs2
.macro  czero_nez rd, rs1, rs2
    .insn r 0x33, 0x7, 0x7, \rd, \rs1, \rs2
.endm
