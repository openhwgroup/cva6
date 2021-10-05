#
# Copyright (C) 2020 by EM Microelectronic US Inc.
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
#
# Generic Exception Test: this directed, manually written test-program covers
#                         many, but not all Exceptions listed in the CV32E40X
#                         exceptions verfication plan plus a number of others
#                         intended to fill holes identified by code coverage.
#
# The pass/fail criteria is determined by checking x26 against MAGIC_NUMBER,
# the value of which is determined by summing the following:
#    - Exception code  2 (Illegal Instruction Exceptions (IIE)): 0x1
#    - Exception code  3 (Breakpoint):                           0x10
#    - Exception code 11 (Environment call):                     0x100
# If the test has one of each exception code, MAGIC_NUMBER is 0x111
#
###############################################################################

#include "corev_uvmt.h"

.globl _start
.globl main
.globl exit
.global debug
.section .text
.global test_results
.global u_sw_irq_handler

    #define MAGIC_NUMBER 0x2f3

test_results:
	.word 123456789
# main test
main:
    li x15, 0x00001800
    csrrw x0, mstatus, x15  # redundant in cv32e40x: hardwired PoR value
    li x0, 0xf21ee7dc
    li x1, 0x80000000
    li x3, 0xccda4374
    li x4, 0x0
    li x5, 0xf4cb539d
    li x6, 0x80000000
    li x7, 0x3
    li x8, 0xfdef1f09
    li x9, 0x80000000
    li x10, 0x4
    li x11, 0xf58fad61
    li x12, 0xfb6606db
    li x13, 0x0
    li x14, 0x0
    li x16, 0x0
    li x17, 0xf61163af
    li x18, 0x0
    li x19, 0x0
    li x20, 0xc552e854
    li x21, 0xc553e854
    li x22, 0xf3ae47cd
    li x23, 0x0
    li x24, 0x00012000
    li x25, 0x80000000
    li x26, 0x0
    li x27, 0xffa38c28
    li x28, 0xf915a8c7
    li x29, 0x9
    li x30, 0x0
    li x31, 0x5912efde
    li x4, 0x40001104
    csrrc x30, mtvec, x0
#2220.000 ns: Illegal instruction (core 0) at PC 0x0000017c:
    .word(0x00000000)	#Exception Code: 2 (illegal instruction)
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    c.ebreak	#Exception Code: 3 (breakpoint)
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    ebreak		#Exception Code: 3 (breakpoint)
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    ecall		#Exception Code: 11 (env call from M-mode)
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    c.addi sp, -8
    sw t0, 4(sp)
    li x15, 0x00001808
    csrs mstatus, x15
    lw t0, 4(sp)
    c.addi sp, 8
#6645.000 ns: Illegal instruction (core 0) at PC 0x000001ec:
    .word(0x00000000)	#Exception Code: 2
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    c.ebreak	#Exception Code: 3
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    ebreak		#Exception Code: 3
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    ecall		#Exception Code: 11
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    lw x0, 0(x24)	#No Exception
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
#11118.000 ns: Illegal instruction (core 0) at PC 0x00000260:
    .word(0x0057179B)   #Exception Code: 2 #SLLIW
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
#12186.000 ns: Illegal instruction (core 0) at PC 0x00000278:
    .word(0x0057579B)   #Exception Code: 2 #SRLIW
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
#13254.000 ns: Illegal instruction (core 0) at PC 0x00000290:
    .word(0x4057579B)   #Exception Code: 2 #SRAIW
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
#14322.000 ns: Illegal instruction (core 0) at PC 0x000002a8:
    csrrc x17, 0x7B0, x0 #Exception Code: 2 #Cannot access DCSR in M mode
    li x18, 0x00008000
    or x17, x17, x18
#15306.000 ns: Illegal instruction (core 0) at PC 0x000002b2:
    csrrw x0, 0x7B0, x17 #Exception Code: 2 #Cannot access DCSR in M mode
#16290.000 ns: Illegal instruction (core 0) at PC 0x000002b6:
    csrrc x17, 0x7B0, x0 #Exception Code: 2 #Cannot access DCSR in M mode
    add x17, x1, x0
    c.addi x17, 12
#17265.000 ns: Illegal instruction (core 0) at PC 0x000002c0:
    csrrw x0, 0x7B1, x17 #Exception Code: 2 #Cannot access DPC in M mode
#18246.000 ns: Illegal instruction (core 0) at PC 0x000002c4:
    csrrc x17, 0x7B1, x0 #Exception Code: 2 #Cannot access DPC in M mode
    ebreak
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop

added_by_mike:
###############################################################################
# Randomly generated illegal instructions.  Each one adds 0x1 to MAGIC_NUMBER
    .word(0x3bc6f92f)
    .word(0x5dd26da7)
    .word(0xe5607a57)
    .word(0x958e4a67)
    .word(0x6159607b)
    .word(0x6c6b7433)
    .word(0x1a6a2b33)
    .word(0xd9067c3b)
    .word(0xfa133223)
    .word(0x6fcbc273)
    .word(0x395dd7e7)
#
    .word(0xaeabed23)
    .word(0xaed5b7a3)
    .word(0xaebf4677)
    .word(0x3bc6f92f)
    .word(0x5dd26da7)
    .word(0xe5607a57)
    .word(0x958e4a67)
    .word(0x6159607b)
    .word(0x6c6b7433)
    .word(0x1a6a2b33)
    .word(0xd9067c3b)
    .word(0xfa133223)
    .word(0x4b724b57)
    .word(0x6fcbc273)
    .word(0x395dd7e7)
    .word(0x079f0c07)
#
    .word(0x57f0f043)
    .word(0xc06d0abb)
    .word(0x75d8b2fb)
    .word(0xd0a96e1b)
    .word(0x2e709e13)
    .word(0x77048bc3)
    .word(0x8b517f2b)
    .word(0x34fcb22f)
    .word(0xf3d1a2af)
    .word(0xd7ac0c9b)
    .word(0x2eeb2953)
    .word(0x3625c82f)
    .word(0x226d459b)
    .word(0x1d4d43ab)
    .word(0xb7aecccf)
    .word(0x1ac1e077)
#
    .word(0x25ffc977)
    .word(0xceb61647)
    .word(0x4284de0f)
    .word(0x585f6a87)
    .word(0x3d1d4d1b)
    .word(0xaf99d353)
    .word(0x27a04dc3)
    .word(0xc6b46abb)
    .word(0x7c18c9b3)
    .word(0x8980c387)
    .word(0xefff246b)
    .word(0xeebb984f)
    .word(0x5724448f)
    .word(0xc964b70f)
    .word(0x58ff393b)
    .word(0xaf9ac3a7)
#
    .word(0x70f6bf03)
    .word(0x9da18a53)
    .word(0x6738ef8f)
    .word(0xf4f4ba5b)
    .word(0xb4208057)
    .word(0x72857967)
    .word(0x64599d9b)
    .word(0x7328b2bb)
    .word(0x9fddb933)
    .word(0x60628efb)
    .word(0xaec951bb)
    .word(0xc56f4a27)
    .word(0x2e266467)
    .word(0xa847620b)
    .word(0x5dd26c27)
    .word(0xb8ba7523)
#
    .word(0x1747bf03)
    .word(0x6e4970cb)
    .word(0xc00624eb)
    .word(0x3847b3bb)
    .word(0x0faf5f9b)
    .word(0xd168d413)
    .word(0x1f6e1d93)
    .word(0x834cd51b)
    .word(0xf787e7eb)
    .word(0x1f9b1a27)
    .word(0x270990eb)
    .word(0xe78c4473)
    .word(0x427706f7)
    .word(0xbcd64e2f)
    .word(0x17f9256b)
    .word(0x4c9cb05b)
#
    .word(0x2ec14d9b)
    .word(0x974ffc9b)
    .word(0xdd91c02f)
    .word(0xc6309677)
    .word(0xf2ddf1e7)
    .word(0xdc656757)
    .word(0x8b454423)
    .word(0x1305370b)
    .word(0x6b235b3b)
    .word(0x6d781c53)
    .word(0xa4b020eb)
    .word(0xf585a0f7)
    .word(0xbd5907f3)
    .word(0x4d4a9e6b)
    .word(0x080f3b7b)
    .word(0x3eaccb2f)
#
    .word(0x4b724b57) # PULP VECOP instruction - will only cause an IIE if XPULP=0
###############################################################################
# Target specific code cov holes in the cv32e40x_decoder.
#
# For OPCODE_SYSTEM (instr_rdata[6:0]=='h73), instr_rdata[31:20] must be one of:
#     12'h000 (ecall), 12'h001 (ebreak),
#     12'h002 (uret),  12'h302 (mret) or 12'h7b2 (dret).
#     Otherwise it is an illegal instruction (add 0x1 to MAGIC_NUMBER).
    .word(0x00300073)
    .word(0x00400073)
    .word(0x30000073)
    .word(0x30100073)
    .word(0x30500073)
    .word(0x7b000073)
    .word(0x7b100073)
    .word(0x7b300073)
    .word(0xf0000073)
# Reading floating point CSRs:FFLAGS, FRM, FCSR (add 0x1 to MAGIC_NUMBER)
    csrrw x0, 0x001, x0 #FFLAGS
    csrrw x0, 0x002, x0 #FRM
    csrrw x0, 0x003, x0 #FCSR
    csrrw x0, 0x807, x0 #FPREC
# Writes to CSRs: MVENDORID, MARCHID, MIMPID, MHARTID (add 0x1 to MAGIC_NUMBER)
    csrrw x0, 0xF11, x0 #MVENDORID
    csrrw x0, 0xF12, x0 #MARCHID
    csrrw x0, 0xF13, x0 #MIMPID
    csrrw x0, 0xF14, x0 #MHARTID
# Writes to to any HPM CSRs (add 0x1 to MAGIC_NUMBER)
    csrrw x0, 0xC00, x0 #CYCLE
    csrrw x0, 0xC02, x0 #INSRET
    csrrw x0, 0xC03, x0 #HPMCOUNTER3
    csrrw x0, 0xC80, x0 #CYCLEH
    csrrw x0, 0xC82, x0 #INSRETH
    csrrw x0, 0xC83, x0 #HPMCOUNTER3H
#Writes to to any User-mode CSRs (add 0x1 to MAGIC_NUMBER)
    csrrw x0, 0x000, x0 #USTATUS
    csrrw x0, 0x041, x0 #UEPC
    csrrw x0, 0x042, x0 #UCAUSE
    csrrw x0, 0x005, x0 #UTVEC
    csrrw x0, 0x004, x0 #UIE      (no specific check of these in the decoder)
    csrrw x0, 0x040, x0 #USCRATCH
    csrrw x0, 0x043, x0 #UTVAL
    csrrw x0, 0x044, x0 #UIP
# p.elw
    .word(0x00006003)   # add 0x1 to MAGIC_NUMBER
    .word(0x00106003)   # add 0x1 to MAGIC_NUMBER
    .word(0x00206003)   # add 0x1 to MAGIC_NUMBER
    .word(0x00406003)   # add 0x1 to MAGIC_NUMBER
    .word(0x00806003)   # add 0x1 to MAGIC_NUMBER
    .word(0x01006003)   # add 0x1 to MAGIC_NUMBER
# uret
    uret                # add 0x1 to MAGIC_NUMBER
# p.elw
    .word(0x02006003)   # add 0x1 to MAGIC_NUMBER
    .word(0x04006003)   # add 0x1 to MAGIC_NUMBER
    .word(0x08006003)   # add 0x1 to MAGIC_NUMBER
    .word(0x10006003)   # add 0x1 to MAGIC_NUMBER
    .word(0x20006003)   # add 0x1 to MAGIC_NUMBER
    .word(0x40006003)   # add 0x1 to MAGIC_NUMBER
    .word(0x80006003)   # add 0x1 to MAGIC_NUMBER
# unused fields in fence (these should _not_ add to MAGIC_NUMBER
    .word(0x00000F8F)   # rd/imm5  =0b11111
    .word(0x000F800F)   # rs1 =0b11111
exit:
    lw x18, test_results /* report passed result */
    li x16, MAGIC_NUMBER
    beq x26, x16, test_end
    li x18, 1
test_end:
    li x17, CV_VP_STATUS_FLAGS_BASE
    sw x18,0(x17)
    j _exit

u_sw_irq_handler:
    addi    sp,sp,-120
    sw      x1,116(sp)
    sw      x2,112(sp)
    sw      x3,108(sp)
    sw      x4,104(sp)
    sw      x5,100(sp)
    sw      x6,96(sp)
    sw      x7,92(sp)
    sw      x8,88(sp)
    sw      x9,84(sp)
    sw      x10,80(sp)
    sw      x11,76(sp)
    sw      x12,72(sp)
    sw      x13,68(sp)
    sw      x14,64(sp)
    sw      x15,60(sp)
    sw      x16,56(sp)
    sw      x17,52(sp)
    sw      x18,48(sp)
    sw      x19,44(sp)
    sw      x20,40(sp)
    sw      x21,36(sp)
    sw      x22,32(sp)
    sw      x23,28(sp)
    sw      x24,24(sp)
    sw      x25,20(sp)
    sw      x28,16(sp)
    sw      x29,12(sp)
    sw      x30,8(sp)
    sw      x31,4(sp)
    c.addi x27, 1
    csrrc x31, mtvec, x0
    beq x31, x30, continue_check
    lui a3, 0x1
    add x26, x26, a3
continue_check:
    li t6, 0xf
    csrrc t5, mcause, x0
    and t6, t6, t5
    li t4, 2
    bne t6, t4, _check_3
    addi x26, x26, 0x1  # illegal instruction (exception code 2): add 0x1 to x26
    csrrc s0, mepc, x0
    c.addi s0, 4
    csrrw x0, mepc, s0
    j _end_trap_Generic_Handler_ASM
_check_3:
    li t4, 3
    bne t6, t4, _check_11
    addi x26, x26, 0x10 # ebreak: add 0x10 to x26
    csrrc s0, mepc, x0
    c.addi s0, 2
    csrrw x0, mepc, s0
    j _end_trap_Generic_Handler_ASM
_check_11:
    li t4, 11
    bne t6, t4, _end_trap_Generic_Handler_ASM
    addi x26, x26, 0x100 # ecall: add 0x100 to x26
    csrrc s0, mepc, x0
    c.addi s0, 4
    csrrw x0, mepc, s0
_end_trap_Generic_Handler_ASM:
    lw      x1,116(sp)
    lw      x2,112(sp)
    lw      x3,108(sp)
    lw      x4,104(sp)
    lw      x5,100(sp)
    lw      x6,96(sp)
    lw      x7,92(sp)
    lw      x8,88(sp)
    lw      x9,84(sp)
    lw      x10,80(sp)
    lw      x11,76(sp)
    lw      x12,72(sp)
    lw      x13,68(sp)
    lw      x14,64(sp)
    lw      x15,60(sp)
    lw      x16,56(sp)
    lw      x17,52(sp)
    lw      x18,48(sp)
    lw      x19,44(sp)
    lw      x20,40(sp)
    lw      x21,36(sp)
    lw      x22,32(sp)
    lw      x23,28(sp)
    lw      x24,24(sp)
    lw      x25,20(sp)
    lw      x28,16(sp)
    lw      x29,12(sp)
    lw      x30,8(sp)
    lw      x31,4(sp)
    addi    sp,sp,120
    mret

_exit:
    j _exit

debug:
    j _exit
