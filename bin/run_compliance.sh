#!/bin/bash

###############################################################################
#
# Copyright 2020 OpenHW Group
# 
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     https://solderpad.org/licenses/
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# 
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################
# run_compliance: runs all test-programs in a specific ISA.
#
# Usage:
#       run_compliance RISCV_ISA
#
# ENV: this script needs the following shell environment variables - 
#       SIM_DIR     : cwd from which to run sims
###############################################################################

cd ${SIM_DIR}

# Script starts here
if [ "$1" == "" ] ; then
    echo "Please specify RISCV_ISA (rv32i|rv32im|rv32imc|rv32Zicsr|rv32Zifencei)"
    exit 1
fi

if [ "$1" == "rv32i" ] || [ "$1" == "rv32im" ] || [ "$1" == "rv32imc" ] || [ "$1" == "rv32Zicsr" ] || [ "$1" == "rv32Zifencei" ] ; then
    echo "nadda"
else
    echo "Unknown RISCV_ISA. Please specify one of rv32i|rv32im|rv32imc|rv32Zicsr|rv32Zifencei"
    exit 1
fi

if [ "$1" == "rv32Zicsr" ] ; then
    make compliance RISCV_ISA=rv32Zicsr COMPLIANCE_PROG=I-CSRRCI-01
    make compliance RISCV_ISA=rv32Zicsr COMPLIANCE_PROG=I-CSRRW-01
    make compliance RISCV_ISA=rv32Zicsr COMPLIANCE_PROG=I-CSRRSI-01
    make compliance RISCV_ISA=rv32Zicsr COMPLIANCE_PROG=I-CSRRC-01
    make compliance RISCV_ISA=rv32Zicsr COMPLIANCE_PROG=I-CSRRWI-01
    make compliance RISCV_ISA=rv32Zicsr COMPLIANCE_PROG=I-CSRRS-01
fi

if [ "$1" == "rv32Zifencei" ]; then
    make compliance RISCV_ISA=rv32Zifencei COMPLIANCE_PROG=I-FENCE.I-01
fi

if [ "$1" == "rv32im" ]; then
    make compliance RISCV_ISA=rv32im COMPLIANCE_PROG=DIV
    make compliance RISCV_ISA=rv32im COMPLIANCE_PROG=MULHU
    make compliance RISCV_ISA=rv32im COMPLIANCE_PROG=REMU
    make compliance RISCV_ISA=rv32im COMPLIANCE_PROG=MULH
    make compliance RISCV_ISA=rv32im COMPLIANCE_PROG=MULHSU
    make compliance RISCV_ISA=rv32im COMPLIANCE_PROG=DIVU
    make compliance RISCV_ISA=rv32im COMPLIANCE_PROG=REM
    make compliance RISCV_ISA=rv32im COMPLIANCE_PROG=MUL
fi

if [ "$1" == "rv32i" ]; then
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-LB-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SUB-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SRAI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ADDI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-BEQ-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SW-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-RF_size-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-LHU-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SLL-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SLTU-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-JALR-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SH-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-BNE-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-LW-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-LH-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-BGE-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SLTI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-BGEU-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ANDI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SRL-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-XORI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ENDIANESS-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SLT-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-LBU-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-RF_width-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ORI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-AND-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-LUI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-BLT-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-NOP-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-XOR-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-AUIPC-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-RF_x0-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SLTIU-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-IO-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SRLI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SB-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SLLI-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-BLTU-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-SRA-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-JAL-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ADD-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-DELAY_SLOTS-01
    make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-OR-01
fi

if [ "$1" == "rv32imc" ]; then
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-SUB
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-ADD
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-SRLI
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-BEQZ
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-J
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-JR
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-SWSP
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-LW
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-ADDI4SPN
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-OR
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-BNEZ
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-LWSP
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-ADDI
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-ADDI16SP
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-SW
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-AND
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-SRAI
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-ANDI
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-LI
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-JALR
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-LUI
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-SLLI
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-XOR
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-MV
    make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=C-JAL
fi

exit 0
