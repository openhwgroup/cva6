#
# Copyright (C) EM Microelectronic US Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
# either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.
#
.globl _start
.globl main
.globl exit
.section .text
.global test_results
test_results:
	.word 123456789
#tests all immediate branching instructions. NOTE: value of register x15 at the end of the test is the error count
main:
# enable interrupts
    li        t0, (0x1 << 3)
    csrs      mstatus, t0
# main test
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
    li x15, 0x0
    li x16, 0x0
    li x17, 0xf61163af
    li x18, 0x0
    li x19, 0x0
    li x20, 0xc552e854
    li x21, 0xc553e854
    li x22, 0xf3ae47cd
    li x23, 0x0
    li x24, 0x0
    li x25, 0x80000000
    li x26, 0xaad8efdc
    li x27, 0xffa38c28
    li x28, 0xf915a8c7
    li x29, 0x9
    li x30, 0x5
    li x31, 0x5912efde
    li x4, 0x40001104
#tests1-6 test the p.beqimm instruction. values loaded in and compared to are expected output values
#p.beqimm is of form "p.beqimm rs1, Imm5, Imm12". Branches to PC + (Imm12 << 1) if rs1==Imm5.
#Imm5 is signed for this instruction
test1:
    li x17, 0x00000005
    p.beqimm x17, 0x05, check1
    c.addi x15, 0x1
    nop
    nop
    nop
check1:
    c.addi x16, 0x1
test2:
    li x17, -10
    p.beqimm x17, -10, check2
    c.addi x15, 0x1
    nop
    nop
check2:
    c.addi x16, 0x1
test3:
    li x17, -3
    p.beqimm x17, -3, check3
    c.addi x15, 0x1
    nop
    nop
    nop
    nop
    nop
    nop
check3:
    c.addi x16, 0x1
test4:
    li x17, 0x00000007
    p.beqimm x17, 0x07, check4
    c.addi x15, 0x1
check4:
    c.addi x16, 0x1
test5:
    li x17, 0x00000000
    p.beqimm x17, 0x01, exit
    c.addi x16, 0x1
test6:
    li x17, -7
    p.beqimm x17, -6, exit
    c.addi x16, 0x1
#tests7-12 test the p.bneimm instruction. values loaded in and compared to are expected output values
#p.bneimm is of form "p.bneimm, rs1, Imm5, Imm 12". Branched to PC + (Imm12 << 1) if rs1==Imm5.
#Imm5 is signed for this instruction
test7: #114
    li x17, 0xffffffff
    p.bneimm x17, 0xe, check7
    c.addi x15, 0x1
    nop
    nop
    nop
check7:
    c.addi x16, 0x1
test8:
    li x17, -10
    p.bneimm x17, -8, check8
    c.addi x15, 0x1
    nop
    nop
check8:
    c.addi x16, 0x1
test9:
    li x17, -3
    p.bneimm x17, 5, check9
    c.addi x15, 0x1
    nop
    nop
    nop
    nop
    nop
    nop
check9:
    c.addi x16, 0x1
test10:
    li x17, 0x00000008
    p.bneimm x17, 0x06, check10
    c.addi x15, 0x1
check10:
    c.addi x16, 0x1
test11:
    li x17, 0x00000000
    p.bneimm x17, 0x00, exit
    c.addi x16, 0x1
test12:
    li x17, -7
    p.bneimm x17, -7, exit_check
    c.addi x16, 0x1
exit_check:
    lw x18, test_results /* report result */
    beq x15, x0, exit
    li x18, 1
exit:
    li x17, 0x20000000
    sw x18,0(x17)
    wfi
