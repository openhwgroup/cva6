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
#tests all general ALU instructions. NOTE: value of register x15 at the end of the test is the error count
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
    li x13, 0x200
    li x14, 0x210
    li x15, 0x0
    li x16, 0xff7811b4
    li x17, 0xf61163af
    li x18, 0x0
    li x19, 0x0
    li x20, 0xc552e854
    li x21, 0xc553e854
    li x22, 0xf3ae47cd
    li x23, 0xc356d985
    li x24, 0x0
    li x25, 0x80000000
    li x26, 0xaad8efdc
    li x27, 0xffa38c28
    li x28, 0xf915a8c7
    li x29, 0x9
    li x30, 0x5
    li x31, 0x5912efde
    li x4, 0x40001104
#tests1-6 test the p.abs instruction. values loaded in and compared to are expected output values
#p.abs instruction is of format "p.abs rD, rs1". rD = rs1 < 0 ? -rs1 : rs1
test1:
    li x20, 0x12577823
    p.abs x18, x20
    li x19, 0x12577823
    beq x18, x19, test2
    c.addi x15, 0x1
test2:
    li x20, 0x85763245
    p.abs x18, x20
    li x19, 0x7a89cdbb
    beq x18, x19, test3
    c.addi x15, 0x1
test3:
    li x20, 0x69879573
    p.abs x18, x20
    li x19, 0x69879573
    beq x18, x19, test4
    c.addi x15, 0x1
test4:
    li x20, 0x98349834
    p.abs x18, x20
    li x19, 0x67cb67cc
    beq x18, x19, test5
    c.addi x15, 0x1
test5:
    li x20, 0x00000000
    p.abs x18, x20
    li x19, 0x00000000
    beq x18, x19, test6
    c.addi x15, 0x1
test6:
    li x20, 0xffffffff
    p.abs x18, x20
    li x19, 0x1
    beq x18, x19, test7
    c.addi x15, 0x1
#tests7-12 test the p.slet instruction. values loaded in and compared to are expected output values
#p.slet instruction is of format "p.slet rD, rs1, rs2". rD = rs1 <= rs2 ? 1 : 0
#comparison is signed
test7:
    li x20, 0x12577823
    li x21, 0x82570957
    p.slet x18, x20, x21
    li x19, 0x0
    beq x18, x19, test8
    c.addi x15, 0x1
test8:
    li x20, 0x85763245
    li x21, 0x84029440
    p.slet x18, x20, x21
    li x19, 0x0
    beq x18, x19, test9
    c.addi x15, 0x1
test9:
    li x20, 0x69879573
    li x21, 0x74014801
    p.slet x18, x20, x21
    li x19, 0x1
    beq x18, x19, test10
    c.addi x15, 0x1
test10:
    li x20, 0x98349834
    li x21, 0x13525363
    p.slet x18, x20, x21
    li x19, 0x1
    beq x18, x19, test11
    c.addi x15, 0x1
test11:
    li x20, 0x00000000
    li x21, 0xffffffff
    p.slet x18, x20, x21
    li x19, 0x0
    beq x18, x19, test12
    c.addi x15, 0x1
test12:
    li x20, 0xffffffff
    li x21, 0xffffffff
    p.slet x18, x20, x21
    li x19, 0x1
    beq x18, x19, test13
    c.addi x15, 0x1
#tests13-18 test the p.sletu instruction. values loaded in and compared to are expected output values
#p.sletu instruction is of format "p.sletu rD, rs1, rs2". rD = rs1 <= rs2 ? 1 : 0
#comparison is unsigned
test13:
    li x20, 0x12577823
    li x21, 0x82570957
    p.sletu x18, x20, x21
    li x19, 0x1
    beq x18, x19, test14
    c.addi x15, 0x1
test14:
    li x20, 0x85763245
    li x21, 0x84029440
    p.sletu x18, x20, x21
    li x19, 0x0
    beq x18, x19, test15
    c.addi x15, 0x1
test15:
    li x20, 0x69879573
    li x21, 0x74014801
    p.sletu x18, x20, x21
    li x19, 0x1
    beq x18, x19, test16
    c.addi x15, 0x1
test16:
    li x20, 0x98349834
    li x21, 0x13525363
    p.sletu x18, x20, x21
    li x19, 0x0
    beq x18, x19, test17
    c.addi x15, 0x1
test17:
    li x20, 0x00000000
    li x21, 0xffffffff
    p.sletu x18, x20, x21
    li x19, 0x1
    beq x18, x19, test18
    c.addi x15, 0x1
test18:
    li x20, 0xffffffff
    li x21, 0xffffffff
    p.sletu x18, x20, x21
    li x19, 0x1
    beq x18, x19, test19
    c.addi x15, 0x1
#tests19-24 test the p.min instruction. values loaded in and compared to are expected output values
#p.min instruction is of format "p.min rD, rs1, rs2". rD = rs1 < rs2 ? rs1 : rs2
#comparison is signed
test19:
    li x20, 0x12577823
    li x21, 0x82570957
    p.min x18, x20, x21
    li x19, 0x82570957
    beq x18, x19, test20
    c.addi x15, 0x1
test20:
    li x20, 0x85763245
    li x21, 0x84029440
    p.min x18, x20, x21
    li x19, 0x84029440
    beq x18, x19, test21
    c.addi x15, 0x1
test21:
    li x20, 0x69879573
    li x21, 0x74014801
    p.min x18, x20, x21
    li x19, 0x69879573
    beq x18, x19, test22
    c.addi x15, 0x1
test22:
    li x20, 0x98349834
    li x21, 0x13525363
    p.min x18, x20, x21
    li x19, 0x98349834
    beq x18, x19, test23
    c.addi x15, 0x1
test23:
    li x20, 0x00000000
    li x21, 0xffffffff
    p.min x18, x20, x21
    li x19, 0xffffffff
    beq x18, x19, test24
    c.addi x15, 0x1
test24:
    li x20, 0xfffffffe
    li x21, 0xffffffff
    p.min x18, x20, x21
    li x19, 0xfffffffe
    beq x18, x19, test25
    c.addi x15, 0x1
#tests25-30 test the p.minu instruction. values loaded in and compared to are expected output values
#p.minu instruction is of format "p.minu rD, rs1, rs2". rD = rs1 < rs2 ? rs1 : rs2
#comparison is unsigned
test25:
    li x20, 0x12577823
    li x21, 0x82570957
    p.minu x18, x20, x21
    li x19, 0x12577823
    beq x18, x19, test26
    c.addi x15, 0x1
test26:
    li x20, 0x85763245
    li x21, 0x84029440
    p.minu x18, x20, x21
    li x19, 0x84029440
    beq x18, x19, test27
    c.addi x15, 0x1
test27:
    li x20, 0x69879573
    li x21, 0x74014801
    p.minu x18, x20, x21
    li x19, 0x69879573
    beq x18, x19, test28
    c.addi x15, 0x1
test28:
    li x20, 0x98349834
    li x21, 0x13525363
    p.minu x18, x20, x21
    li x19, 0x13525363
    beq x18, x19, test29
    c.addi x15, 0x1
test29:
    li x20, 0x00000000
    li x21, 0xffffffff
    p.minu x18, x20, x21
    li x19, 0x00000000
    beq x18, x19, test30
    c.addi x15, 0x1
test30:
    li x20, 0xfffffffe
    li x21, 0xffffffff
    p.minu x18, x20, x21
    li x19, 0xfffffffe
    beq x18, x19, test31
    c.addi x15, 0x1
#tests31-36 test the p.max instruction. values loaded in and compared to are expected output values
#p.max instruction is of format "p.max rD, rs1, rs2". rD = rs1 < rs2 ? rs2 : rs1
#comparison is signed
test31:
    li x20, 0x12577823
    li x21, 0x82570957
    p.max x18, x20, x21
    li x19, 0x12577823
    beq x18, x19, test32
    c.addi x15, 0x1
test32:
    li x20, 0x85763245
    li x21, 0x84029440
    p.max x18, x20, x21
    li x19, 0x85763245
    beq x18, x19, test33
    c.addi x15, 0x1
test33:
    li x20, 0x69879573
    li x21, 0x74014801
    p.max x18, x20, x21
    li x19, 0x74014801
    beq x18, x19, test34
    c.addi x15, 0x1
test34:
    li x20, 0x98349834
    li x21, 0x13525363
    p.max x18, x20, x21
    li x19, 0x13525363
    beq x18, x19, test35
    c.addi x15, 0x1
test35:
    li x20, 0x00000000
    li x21, 0xffffffff
    p.max x18, x20, x21
    li x19, 0x00000000
    beq x18, x19, test36
    c.addi x15, 0x1
test36:
    li x20, 0xffffffff
    li x21, 0xfffffffe
    p.max x18, x20, x21
    li x19, 0xffffffff
    beq x18, x19, test37
    c.addi x15, 0x1
#tests37-42 test the p.maxu instruction. values loaded in and compared to are expected output values
#p.maxu instruction is of format "p.maxu rD, rs1, rs2". rD = rs1 < rs2 ? rs2 : rs1
#comparison is unsigned
test37:
    li x20, 0x12577823
    li x21, 0x82570957
    p.maxu x18, x20, x21
    li x19, 0x82570957
    beq x18, x19, test38
    c.addi x15, 0x1
test38:
    li x20, 0x85763245
    li x21, 0x84029440
    p.maxu x18, x20, x21
    li x19, 0x85763245
    beq x18, x19, test39
    c.addi x15, 0x1
test39:
    li x20, 0x69879573
    li x21, 0x74014801
    p.maxu x18, x20, x21
    li x19, 0x74014801
    beq x18, x19, test40
    c.addi x15, 0x1
test40:
    li x20, 0x98349834
    li x21, 0x13525363
    p.maxu x18, x20, x21
    li x19, 0x98349834
    beq x18, x19, test41
    c.addi x15, 0x1
test41:
    li x20, 0x00000000
    li x21, 0xffffffff
    p.maxu x18, x20, x21
    li x19, 0xffffffff
    beq x18, x19, test42
    c.addi x15, 0x1
test42:
    li x20, 0xffffffff
    li x21, 0xfffffffe
    p.maxu x18, x20, x21
    li x19, 0xffffffff
    beq x18, x19, test43
    c.addi x15, 0x1
#tests43-48 test the p.exths instruction. values loaded in and compared to are expected output values
#p.exths instruction is of format "p.exths rD, rs1". rD = Sext(rs1[15:0])
test43:
    li x20, 0x12577823
    p.exths x18, x20
    li x19, 0x00007823
    beq x18, x19, test44
    c.addi x15, 0x1
test44:
    li x20, 0x85763245
    p.exths x18, x20
    li x19, 0x00003245
    beq x18, x19, test45
    c.addi x15, 0x1
test45:
    li x20, 0x69879573
    p.exths x18, x20
    li x19, 0xffff9573
    beq x18, x19, test46
    c.addi x15, 0x1
test46:
    li x20, 0x98349834
    p.exths x18, x20
    li x19, 0xffff9834
    beq x18, x19, test47
    c.addi x15, 0x1
test47:
    li x20, 0x00000000
    p.exths x18, x20
    li x19, 0x00000000
    beq x18, x19, test48
    c.addi x15, 0x1
test48:
    li x20, 0xffffffff
    p.exths x18, x20
    li x19, 0xffffffff
    beq x18, x19, test49
    c.addi x15, 0x1
#tests49-54 test the p.exthz instruction. values loaded in and compared to are expected output values
#p.exthz instruction is of format "p.exthz rD, rs1". rD = Zext(rs1[15:0])
test49:
    li x20, 0x12577823
    p.exthz x18, x20
    li x19, 0x00007823
    beq x18, x19, test50
    c.addi x15, 0x1
test50:
    li x20, 0x85763245
    p.exthz x18, x20
    li x19, 0x00003245
    beq x18, x19, test51
    c.addi x15, 0x1
test51:
    li x20, 0x69879573
    p.exthz x18, x20
    li x19, 0x00009573
    beq x18, x19, test52
    c.addi x15, 0x1
test52:
    li x20, 0x98349834
    p.exthz x18, x20
    li x19, 0x00009834
    beq x18, x19, test53
    c.addi x15, 0x1
test53:
    li x20, 0x00000000
    p.exthz x18, x20
    li x19, 0x00000000
    beq x18, x19, test54
    c.addi x15, 0x1
test54:
    li x20, 0xffffffff
    p.exthz x18, x20
    li x19, 0x0000ffff
    beq x18, x19, test55
    c.addi x15, 0x1
#tests55-60 test the p.extbs instruction. values loaded in and compared to are expected output values
#p.extbs instruction is of format "p.extbs rD, rs1". rD = Sext(rs1[7:0])
test55:
    li x20, 0x12577823
    p.extbs x18, x20
    li x19, 0x00000023
    beq x18, x19, test56
    c.addi x15, 0x1
test56:
    li x20, 0x857632a5
    p.extbs x18, x20
    li x19, 0xffffffa5
    beq x18, x19, test57
    c.addi x15, 0x1
test57:
    li x20, 0x69879583
    p.extbs x18, x20
    li x19, 0xffffff83
    beq x18, x19, test58
    c.addi x15, 0x1
test58:
    li x20, 0x98349834
    p.extbs x18, x20
    li x19, 0x00000034
    beq x18, x19, test59
    c.addi x15, 0x1
test59:
    li x20, 0x00000000
    p.extbs x18, x20
    li x19, 0x00000000
    beq x18, x19, test60
    c.addi x15, 0x1
test60:
    li x20, 0xffffffff
    p.extbs x18, x20
    li x19, 0xffffffff
    beq x18, x19, test61
    c.addi x15, 0x1
#tests61-66 test the p.extbz instruction. values loaded in and compared to are expected output values
#p.extbz instruction is of format "p.extbz rD, rs1". rD = Zext(rs1[7:0])
test61:
    li x20, 0x12577823
    p.extbz x18, x20
    li x19, 0x00000023
    beq x18, x19, test62
    c.addi x15, 0x1
test62:
    li x20, 0x85763245
    p.extbz x18, x20
    li x19, 0x00000045
    beq x18, x19, test63
    c.addi x15, 0x1
test63:
    li x20, 0x69879573
    p.extbz x18, x20
    li x19, 0x00000073
    beq x18, x19, test64
    c.addi x15, 0x1
test64:
    li x20, 0x98349834
    p.extbz x18, x20
    li x19, 0x00000034
    beq x18, x19, test65
    c.addi x15, 0x1
test65:
    li x20, 0x00000000
    p.extbz x18, x20
    li x19, 0x00000000
    beq x18, x19, test66
    c.addi x15, 0x1
test66:
    li x20, 0xffffffff
    p.extbz x18, x20
    li x19, 0x000000ff
    beq x18, x19, test67
    c.addi x15, 0x1
#tests67-72 test the p.clip instruction. values loaded in and compared to are expected output values
#p.clip instruction is of format "p.clip rD, rs1, ls2". if rs1 <= -2^(ls2-1), rD = -2^(ls2-1)
#or if rs1 >= 2^(ls2-1), rD = 2^(ls2-1)-1, else rD = rs1
test67:
    li x20, 0x12577823
    p.clip x18, x20, 15
    li x19, 0x00003fff
    beq x18, x19, test68
    c.addi x15, 0x1
test68:
    li x20, 0x85763245
    p.clip x18, x20, 26
    li x19, 0xfe000000
    beq x18, x19, test69
    c.addi x15, 0x1
test69:
    li x20, 0x69879573
    p.clip x18, x20, 31
    li x19, 0x3fffffff
    beq x18, x19, test70
    c.addi x15, 0x1
test70:
    li x20, 0x98349834
    p.clip x18, x20, 31
    li x19, 0xc0000000
    beq x18, x19, test71
    c.addi x15, 0x1
test71:
    li x20, 0x00000000
    p.clip x18, x20, 10
    li x19, 0x00000000
    beq x18, x19, test72
    c.addi x15, 0x1
test72:
    li x20, 0xffffffff
    p.clip x18, x20, 6
    li x19, 0xffffffff
    beq x18, x19, test73
    c.addi x15, 0x1
#tests73-78 test the p.clipr instruction. values loaded in and compared to are expected output values
#p.clipr instruction is of format "p.clipr rD, rs1, rs2". if rs1 <= -(rs2+1), rD = -(rs2+1)
#or if rs1 >= rs2, rD = rs2, else rD = rs1
test73:
    li x20, 0x12577823
    li x21, 0x08095074
    p.clipr x18, x20, x21
    li x19, 0x08095074
    beq x18, x19, test74
    c.addi x15, 0x1
test74:
    li x20, 0x85763245
    li x21, 0x00405809
    p.clipr x18, x20, x21
    li x19, 0xffbfa7f6
    beq x18, x19, test75
    c.addi x15, 0x1
test75:
    li x20, 0x69879573
    li x21, 0x698f9097
    p.clipr x18, x20, x21
    li x19, 0x69879573
    beq x18, x19, test76
    c.addi x15, 0x1
test76:
    li x20, 0x98349834
    li x21, 0x7f000000
    p.clipr x18, x20, x21
    li x19, 0x98349834
    beq x18, x19, test77
    c.addi x15, 0x1
test77:
    li x20, 0x00000000
    li x21, 0x70908094
    p.clipr x18, x20, x21
    li x19, 0x00000000
    beq x18, x19, test78
    c.addi x15, 0x1
test78:
    li x20, 0xffffffff
    li x21, 0x70988098
    p.clipr x18, x20, x21
    li x19, 0xffffffff
    beq x18, x19, test79
    c.addi x15, 0x1
#tests79-84 test the p.clipu instruction. values loaded in and compared to are expected output values
#p.clipu instruction is of format "p.clipu rD, rs1, ls2". if rs1 <= 0, rD = 0
#or if rs1 >= 2^(ls2-1), rD = 2^(ls2-1)-1, else rD = rs1
test79:
    li x20, 0x12577823
    p.clipu x18, x20, 15
    li x19, 0x00003fff
    beq x18, x19, test80
    c.addi x15, 0x1
test80:
    li x20, 0x85763245
    p.clipu x18, x20, 26
    li x19, 0x0
    beq x18, x19, test81
    c.addi x15, 0x1
test81:
    li x20, 0x69879573
    p.clipu x18, x20, 31
    li x19, 0x3fffffff
    beq x18, x19, test82
    c.addi x15, 0x1
test82:
    li x20, 0x98349834
    p.clipu x18, x20, 31
    li x19, 0x0
    beq x18, x19, test83
    c.addi x15, 0x1
test83:
    li x20, 0x00000000
    p.clipu x18, x20, 10
    li x19, 0x00000000
    beq x18, x19, test84
    c.addi x15, 0x1
test84:
    li x20, 0xffffffff
    p.clipu x18, x20, 6
    li x19, 0x0
    beq x18, x19, test85
    c.addi x15, 0x1
#tests85-90 test the p.clipur instruction. values loaded in and compared to are expected output values
#p.clipur instruction is of format "p.clipur rD, rs1, rs2". if rs1 <= -(rs2+1), rD = -(rs2+1)
#or if rs1 >= rs2, rD = rs2, else rD = rs1
test85:
    li x20, 0x12577825
    li x21, 0x08095074
    p.clipur x18, x20, x21
    li x19, 0x08095074
    beq x18, x19, test86
    c.addi x15, 0x1
test86:
    li x20, 0x85763245
    li x21, 0x00405809
    p.clipur x18, x20, x21
    li x19, 0x0
    beq x18, x19, test87
    c.addi x15, 0x1
test87:
    li x20, 0x69879573
    li x21, 0x698f9097
    p.clipur x18, x20, x21
    li x19, 0x69879573
    beq x18, x19, test88
    c.addi x15, 0x1
test88:
    li x20, 0x98349834
    li x21, 0x7f000000
    p.clipur x18, x20, x21
    li x19, 0x0
    beq x18, x19, test89
    c.addi x15, 0x1
test89:
    li x20, 0x00000000
    li x21, 0x70908094
    p.clipur x18, x20, x21
    li x19, 0x00000000
    beq x18, x19, test90
    c.addi x15, 0x1
test90:
    li x20, 0xffffffff
    li x21, 0x70988098
    p.clipur x18, x20, x21
    li x19, 0x0
    beq x18, x19, test91
    c.addi x15, 0x1
#tests91-96 test the p.addN instruction. values loaded in andcompared to are expected output values
#p.addN instruction is of format "p.addN rD, rs1, rs2, ls3". rD = (rs1 + rs2) >>> ls3
test91:
    li x20, 0x72936987
    li x21, 0x09734009
    p.addN x18, x20, x21, 4
    li x19, 0x07c06a99
    beq x18, x19, test92
    c.addi x15, 0x1
test92:
    li x20, 0x6bac0f09
    li x21, 0x9f8fae8c
    p.addN x18, x20, x21, 6
    li x19, 0x2ceef6
    beq x18, x19, test93
    c.addi x15, 0x1
test93:
    li x20, 0x42346c3a
    li x21, 0x5f877f8f
    p.addN x18, x20, x21, 0xd 
    li x19, 0xfffd0ddf
    beq x18, x19, test94
    c.addi x15, 0x1
test94:
    li x20, 0xc3dc9c1f
    li x21, 0xe396652a
    p.addN x18, x20, x21, 9
    li x19, 0xffd3b980
    beq x18, x19, test95
    c.addi x15, 0x1
test95:
    li x20, 0x44587ccc
    li x21, 0x452a294f
    p.addN x18, x20, x21, 0x18
    li x19, 0xffffff89
    beq x18, x19, test96
    c.addi x15, 0x1
test96:
    li x20, 0x11c7b074
    li x21, 0x57e03f4b
    p.addN x18, x20, x21, 10
    li x19, 0x001a69fb
    beq x18, x19, test97
    c.addi x15, 0x1
#tests97-102 test the p.adduN instruction. values loaded in andcompared to are expected output values
#p.adduN instruction is of format "p.adduN rD, rs1, rs2, ls3". rD = (rs1 + rs2) >> ls3
test97:
    li x20, 0xb2157f04
    li x21, 0xb5bf1b07
    p.adduN x18, x20, x21, 0xe
    li x19, 0x00019f52
    beq x18, x19, test98
    c.addi x15, 0x1
test98:
    li x20, 0x398f97d9
    li x21, 0x41f67bbb
    p.adduN x18, x20, x21, 0xc
    li x19, 0x0007b861
    beq x18, x19, test99
    c.addi x15, 0x1
test99:
    li x20, 0x75157c72
    li x21, 0xe2969e22
    p.adduN x18, x20, x21, 3
    li x19, 0x0af58352
    beq x18, x19, test100
    c.addi x15, 0x1
test100:
    li x20, 0x6b6c6895
    li x21, 0x08dfc119
    p.adduN x18, x20, x21, 0xf
    li x19, 0x0000e898
    beq x18, x19, test101
    c.addi x15, 0x1
test101:
    li x20, 0xf989a204
    li x21, 0xe3cc5625
    p.adduN x18, x20, x21, 6
    li x19, 0x037557e0
    beq x18, x19, test102
    c.addi x15, 0x1
test102:
    li x20, 0x4b31472c
    li x21, 0x782df448
    p.adduN x18, x20, x21, 0xc
    li x19, 0x000c35f3
    beq x18, x19, test103
    c.addi x15, 0x1
#tests103-108 test the p.addRN instruction. values loaded in andcompared to are expected output values
#p.addRN instruction is of format "p.addRN rD, rs1, rs2, ls3". rD = (rs1 + rs2 + 2^(ls3-1)) >>> ls3
test103:
    li x20, 0xec5864c5
    li x21, 0xaf202e1f
    p.addRN x18, x20, x21, 0xe
    li x19, 0xfffe6de2
    beq x18, x19, test104
    c.addi x15, 0x1
test104:
    li x20, 0xa117f390
    li x21, 0x502f1a97
    p.addRN x18, x20, x21, 0xc
    li x19, 0xffff1471
    beq x18, x19, test105
    c.addi x15, 0x1
test105:
    li x20, 0x0e573f8d
    li x21, 0x53e33b97
    p.addRN x18, x20, x21, 0x1e
    li x19, 0xfffffffe
    beq x18, x19, test106
    c.addi x15, 0x1
test106:
    li x20, 0xd9231dc0
    li x21, 0xcdefaa4c
    p.addRN x18, x20, x21, 0xa
    li x19, 0xffe9c4b2
    beq x18, x19, test107
    c.addi x15, 0x1
test107:
    li x20, 0x2cddf47b
    li x21, 0x3ecdc49d
    p.addRN x18, x20, x21, 4
    li x19, 0x06babb92
    beq x18, x19, test108
    c.addi x15, 0x1
test108:
    li x20, 0x5f32c376
    li x21, 0x1cb579cf
    p.addRN x18, x20, x21, 0xf
    li x19, 0x0000f7d0
    beq x18, x19, test109
    c.addi x15, 0x1
#tests109-114 test the p.adduRN instruction. values loaded in andcompared to are expected output values
#p.adduRN instruction is of format "p.adduRN rD, rs1, rs2, ls3". rD = (rs1 + rs2 + 2^(ls3-1)) >> ls3
test109:
    li x20, 0xc5e72ff3
    li x21, 0x7aedfaa4
    p.adduRN x18, x20, x21, 0xa
    li x19, 0x0010354b
    beq x18, x19, test110
    c.addi x15, 0x1
test110:
    li x20, 0xb819c9fc
    li x21, 0x9a4797c0
    p.adduRN x18, x20, x21, 3
    li x19, 0x0a4c2c38
    beq x18, x19, test111
    c.addi x15, 0x1
test111:
    li x20, 0x5b1db039
    li x21, 0xac2fbd67
    p.adduRN x18, x20, x21, 9
    li x19, 0x0003a6b7
    beq x18, x19, test112
    c.addi x15, 0x1
test112:
    li x20, 0x190fe0d1
    li x21, 0xb26a9865
    p.adduRN x18, x20, x21, 0xa
    li x19, 0x0032de9e
    beq x18, x19, test113
    c.addi x15, 0x1
test113:
    li x20, 0x20d5dd4a
    li x21, 0x58838351
    p.adduRN x18, x20, x21, 0xb
    li x19, 0x000f2b2c
    beq x18, x19, test114
    c.addi x15, 0x1
test114:
    li x20, 0x6137c87d
    li x21, 0x5e197fed
    p.adduRN x18, x20, x21, 0xd
    li x19, 0x0005fa8a
    beq x18, x19, test115
    c.addi x15, 0x1
#tests115-120 test the p.addNr instruction. values loaded in andcompared to are expected output values
#p.addNr instruction is of format "p.addNr rD, rs1, rs2". rD = (rD + rs1) >>> rs2[4:0]
test115:
    li x18, 0x646f6bd5
    li x20, 0x2d4ffc3b
    li x21, 0xed7354c3
    p.addNr x18, x20, x21
    li x19, 0xf237ed02
    beq x18, x19, test116
    c.addi x15, 0x1
test116:
    li x18, 0xb86e922f
    li x20, 0x5f242322
    li x21, 0x6e2fe71a
    p.addNr x18, x20, x21
    li x19, 0x00000005
    beq x18, x19, test117
    c.addi x15, 0x1
test117:
    li x18, 0xced663d0
    li x20, 0xf8fc447c
    li x21, 0x52c0d7df
    p.addNr x18, x20, x21
    li x19, 0xffffffff
    beq x18, x19, test118
    c.addi x15, 0x1
test118:
    li x18, 0xc1ef74f9
    li x20, 0xe9ee71b6
    li x21, 0x219106a7
    p.addNr x18, x20, x21
    li x19, 0xff57bbcd
    beq x18, x19, test119
    c.addi x15, 0x1
test119:
    li x18, 0x3a5c81d2
    li x20, 0xb09e0fb3
    li x21, 0xf3251a70
    p.addNr x18, x20, x21
    li x19, 0xffffeafa
    beq x18, x19, test120
    c.addi x15, 0x1
test120:
    li x18, 0xa5b921bf
    li x20, 0xcead29a4
    li x21, 0x5dd92029
    p.addNr x18, x20, x21
    li x19, 0x003a3325
    beq x18, x19, test121
    c.addi x15, 0x1
#tests121-126 test the p.adduNr instruction. values loaded in andcompared to are expected output values
#p.adduNr instruction is of format "p.adduNr rD, rs1, rs2". rD = (rD + rs1) >> rs2[4:0]
test121:
    li x18, 0x65cef5d7
    li x20, 0x60e59b8a
    li x21, 0x9d36df4b
    p.adduNr x18, x20, x21
    li x19, 0x0018d692
    beq x18, x19, test122
    c.addi x15, 0x1
test122:
    li x18, 0xba2a731d
    li x20, 0x6e9335ba
    li x21, 0x4b174fd0
    p.adduNr x18, x20, x21
    li x19, 0x000028bd
    beq x18, x19, test123
    c.addi x15, 0x1
test123:
    li x18, 0x9264b71c
    li x20, 0x7aada0de
    li x21, 0xaa66eb7c
    p.adduNr x18, x20, x21
    li x19, 0x00000000
    beq x18, x19, test124
    c.addi x15, 0x1
test124:
    li x18, 0xee8a2c3b
    li x20, 0xc2bfab6b
    li x21, 0xab36de09
    p.adduNr x18, x20, x21
    li x19, 0x0058a4eb
    beq x18, x19, test125
    c.addi x15, 0x1
test125:
    li x18, 0x8bcaf600
    li x20, 0x0ea2c360
    li x21, 0x05984e93
    p.adduNr x18, x20, x21
    li x19, 0x0000134d
    beq x18, x19, test126
    c.addi x15, 0x1
test126:
    li x18, 0x52658344
    li x20, 0x1f77523b
    li x21, 0xfacb520d
    p.adduNr x18, x20, x21
    li x19, 0x00038ee6
    beq x18, x19, test127
    c.addi x15, 0x1
#tests127-132 test the p.addRNr instruction. values loaded in and compared to are expected output values
#p.addRNr instruction is of format "p.addRNr rD, rs1, rs2". rD = (rD + rs1 + 2^(rs2[4:0]-1)) >>> rs2[4:0]
test127:
    li x18, 0x913c3879
    li x20, 0x964b68d4
    li x21, 0x361922fa
    p.addRNr x18, x20, x21
    li x19, 0x0000000a
    beq x18, x19, test128
    c.addi x15, 0x1
test128:
    li x18, 0x03f7a125
    li x20, 0xa3c9eccd
    li x21, 0x1be630b7
    p.addRNr x18, x20, x21
    li x19, 0xffffff50
    beq x18, x19, test129
    c.addi x15, 0x1
test129:
    li x18, 0x34b63af5
    li x20, 0xa5e12c0c
    li x21, 0xd51e66eb
    p.addRNr x18, x20, x21
    li x19, 0xfffb52ed
    beq x18, x19, test130
    c.addi x15, 0x1
test130:
    li x18, 0xff1aa145
    li x20, 0xfdf121e1
    li x21, 0x0b58d4ec
    p.addRNr x18, x20, x21
    li x19, 0xffffd0bc
    beq x18, x19, test131
    c.addi x15, 0x1
test131:
    li x18, 0x97251982
    li x20, 0x00488629
    li x21, 0xc5f54aeb
    p.addRNr x18, x20, x21
    li x19, 0xfff2edb4
    beq x18, x19, test132
    c.addi x15, 0x1
test132:
    li x18, 0x3968f2d8
    li x20, 0x2429ff2f
    li x21, 0x9819e086
    p.addRNr x18, x20, x21
    li x19, 0x01764bc8
    beq x18, x19, test133
    c.addi x15, 0x1
#tests133-138 test the p.adduRNr instruction. values loaded in and compared to are expected output values
#p.adduRNr instruction is of format "p.adduRNr rD, rs1, rs2". rD = (rD + rs1 + 2^(rs2[4:0]-1)) >> rs2[4:0]
test133:
    li x18, 0x456a58c7
    li x20, 0x41487a7d
    li x21, 0x106418ac
    p.adduRNr x18, x20, x21
    li x19, 0x00086b2d
    beq x18, x19, test134
    c.addi x15, 0x1
test134:
    li x18, 0x71fa9839
    li x20, 0x991bcb1d
    li x21, 0x4de92911
    p.adduRNr x18, x20, x21
    li x19, 0x0000058b
    beq x18, x19, test135
    c.addi x15, 0x1
test135:
    li x18, 0xaa581c17
    li x20, 0x3943efaf
    li x21, 0x729929d9
    p.adduRNr x18, x20, x21
    li x19, 0x00000072
    beq x18, x19, test136
    c.addi x15, 0x1
test136:
    li x18, 0x67358b2d
    li x20, 0xf1f9706f
    li x21, 0xea5711bf
    p.adduRNr x18, x20, x21
    li x19, 0x00000001
    beq x18, x19, test137
    c.addi x15, 0x1
test137:
    li x18, 0x616d6b1a
    li x20, 0x675fa4d2
    li x21, 0x2f7243c9
    p.adduRNr x18, x20, x21
    li x19, 0x00646688
    beq x18, x19, test138
    c.addi x15, 0x1
test138:
    li x18, 0xbfdf721a
    li x20, 0xd2082e34
    li x21, 0x640e1c44
    p.adduRNr x18, x20, x21
    li x19, 0x091e7a05
    beq x18, x19, test139
    c.addi x15, 0x1
#tests139-144 test the p.subN instruction. values loaded in andcompared to are expected output values
#p.subN instruction is of format "p.subN rD, rs1, rs2, ls3". rD = (rs1 - rs2) >>> ls3
test139:
    li x20, 0x2d221d9b
    li x21, 0x104bfa70
    p.subN x18, x20, x21, 8
    li x19, 0x01cd623
    beq x18, x19, test140
    c.addi x15, 0x1
test140:
    li x20, 0x7e089f95
    li x21, 0x449323b6
    p.subN x18, x20, x21, 5
    li x19, 0x01cbabde
    beq x18, x19, test141
    c.addi x15, 0x1
test141:
    li x20, 0xa74931fa
    li x21, 0x9b7131e3
    p.subN x18, x20, x21, 7
    li x19, 0x0017b000
    beq x18, x19, test142
    c.addi x15, 0x1
test142:
    li x20, 0x1dd4997f
    li x21, 0x53a6e152
    p.subN x18, x20, x21, 0xc
    li x19, 0xfffca2db
    beq x18, x19, test143
    c.addi x15, 0x1
test143:
    li x20, 0xa17c64d6
    li x21, 0x313e6061
    p.subN x18, x20, x21, 0x10
    li x19, 0x0000703e
    beq x18, x19, test144
    c.addi x15, 0x1
test144:
    li x20, 0xe081ba5c
    li x21, 0x0de1ad03
    p.subN x18, x20, x21, 0x12
    li x19, 0xfffff4a8
    beq x18, x19, test145
    c.addi x15, 0x1
#tests145-150 test the p.subuN instruction. values loaded in andcompared to are expected output values
#p.subuN instruction is of format "p.subuN rD, rs1, rs2, ls3". rD = (rs1 - rs2) >> ls3
test145:
    li x20, 0xa59ad94e
    li x21, 0xc473a2ea
    p.subuN x18, x20, x21, 3
    li x19, 0x1c24e6cc
    beq x18, x19, test146
    c.addi x15, 0x1
test146:
    li x20, 0x3208375a
    li x21, 0x4aef0ff0
    p.subuN x18, x20, x21, 0xb
    li x19, 0x001ce324
    beq x18, x19, test147
    c.addi x15, 0x1
test147:
    li x20, 0xc266172f
    li x21, 0x326303a7
    p.subuN x18, x20, x21, 2
    li x19, 0x2400c4e2
    beq x18, x19, test148
    c.addi x15, 0x1
test148:
    li x20, 0x430eb2ba
    li x21, 0xe5639f98
    p.subuN x18, x20, x21, 0x11
    li x19, 0x00002ed5
    beq x18, x19, test149
    c.addi x15, 0x1
test149:
    li x20, 0x7be90b07
    li x21, 0x46d56a8c
    p.subuN x18, x20, x21, 9
    li x19, 0x001a89d0
    beq x18, x19, test150
    c.addi x15, 0x1
test150:
    li x20, 0x0e16c7cf
    li x21, 0x9219530c
    p.subuN x18, x20, x21, 0x12
    li x19, 0x00001eff
    beq x18, x19, test151
    c.addi x15, 0x1
#tests151-156 test the p.subRN instruction. values loaded in andcompared to are expected output values
#p.subRN instruction is of format "p.subRN rD, rs1, rs2, ls3". rD = (rs1 - rs2 + 2^(ls3-1)) >>> ls3
test151:
    li x20, 0x84ac1cee
    li x21, 0xd2fb2d2d
    p.subRN x18, x20, x21, 0x11
    li x19, 0xffffd8d8
    beq x18, x19, test152
    c.addi x15, 0x1
test152:
    li x20, 0xe3db1897
    li x21, 0x04855369
    p.subRN x18, x20, x21, 0xc
    li x19, 0xfffdf55c
    beq x18, x19, test153
    c.addi x15, 0x1
test153:
    li x20, 0xadc655f1
    li x21, 0x4aafcf57
    p.subRN x18, x20, x21, 0xb
    li x19, 0x000c62d1
    beq x18, x19, test154
    c.addi x15, 0x1
test154:
    li x20, 0x4623ef1d
    li x21, 0x30f7be5a
    p.subRN x18, x20, x21, 0x17
    li x19, 0x0000002a
    beq x18, x19, test155
    c.addi x15, 0x1
test155:
    li x20, 0xac15aded
    li x21, 0xe3ec3b7c
    p.subRN x18, x20, x21, 4
    li x19, 0xfc829727
    beq x18, x19, test156
    c.addi x15, 0x1
test156:
    li x20, 0xa6256e0b
    li x21, 0xd4e8f056
    p.subRN x18, x20, x21, 0xa
    li x19, 0xfff44f1f
    beq x18, x19, test157
    c.addi x15, 0x1
#tests157-162 test the p.subuRN instruction. values loaded in andcompared to are expected output values
#p.subuRN instruction is of format "p.subuRN rD, rs1, rs2, ls3". rD = (rs1 - rs2 + 2^(ls3-1)) >> ls3
test157:
    li x20, 0x84ac1cee
    li x21, 0xd2fb2d2d
    p.subuRN x18, x20, x21, 0x11
    li x19, 0x000058d8
    beq x18, x19, test158
    c.addi x15, 0x1
test158:
    li x20, 0xe3db1897
    li x21, 0x04855369
    p.subuRN x18, x20, x21, 0xc
    li x19, 0x000df55c
    beq x18, x19, test159
    c.addi x15, 0x1
test159:
    li x20, 0xadc655f1
    li x21, 0x4aafcf57
    p.subuRN x18, x20, x21, 0xb
    li x19, 0x000c62d1
    beq x18, x19, test160
    c.addi x15, 0x1
test160:
    li x20, 0x4623ef1d
    li x21, 0x30f7be5a
    p.subuRN x18, x20, x21, 0x17
    li x19, 0x0000002a
    beq x18, x19, test161
    c.addi x15, 0x1
test161:
    li x20, 0xac15aded
    li x21, 0xe3ec3b7c
    p.subuRN x18, x20, x21, 4
    li x19, 0x0c829727
    beq x18, x19, test162
    c.addi x15, 0x1
test162:
    li x20, 0xa6256e0b
    li x21, 0xd4e8f056
    p.subuRN x18, x20, x21, 0xa
    li x19, 0x00344f1f
    beq x18, x19, test163
    c.addi x15, 0x1
#tests163-168 test the p.subNr instruction. values loaded in andcompared to are expected output values
#p.subNr instruction is of format "p.subNr rD, rs1, rs2". rD = (rD - rs1) >>> rs2[4:0]
test163:
    li x18, 0x8c178e58
    li x20, 0xbec1d356
    li x21, 0x35a0de16
    p.subNr x18, x20, x21
    li x19, 0xffffff35
    beq x18, x19, test164
    c.addi x15, 0x1
test164:
    li x18, 0x5a755dcc
    li x20, 0x42daab66
    li x21, 0xdfed16a2
    p.subNr x18, x20, x21
    li x19, 0x05e6ac99
    beq x18, x19, test165
    c.addi x15, 0x1
test165:
    li x18, 0x20d46d05
    li x20, 0x8e2d2a35
    li x21, 0xcf7c564b
    p.subNr x18, x20, x21
    li x19, 0xfff254e8
    beq x18, x19, test166
    c.addi x15, 0x1
test166:
    li x18, 0x5fc53a5c
    li x20, 0x0bbe1773
    li x21, 0x905a118f
    p.subNr x18, x20, x21
    li x19, 0x0000a80e
    beq x18, x19, test167
    c.addi x15, 0x1
test167:
    li x18, 0xe18fe383
    li x20, 0xea4821e3
    li x21, 0x1ac9f4f7
    p.subNr x18, x20, x21
    li x19, 0xffffffee
    beq x18, x19, test168
    c.addi x15, 0x1
test168:
    li x18, 0x54596448
    li x20, 0x44756aa2
    li x21, 0x22128b2e
    p.subNr x18, x20, x21
    li x19, 0x00003f8f
    beq x18, x19, test169
    c.addi x15, 0x1
#tests169-174 test the p.subuNr instruction. values loaded in andcompared to are expected output values
#p.subuNr instruction is of format "p.subuNr rD, rs1, rs2". rD = (rD - rs1) >> rs2[4:0]
test169:
    li x18, 0xcc3fa958
    li x20, 0xcc9ba04b
    li x21, 0x683854e2
    p.subuNr x18, x20, x21
    li x19, 0x3fe90243
    beq x18, x19, test170
    c.addi x15, 0x1
test170:
    li x18, 0x6a494b61
    li x20, 0x30c8745d
    li x21, 0xbe0eb1a4
    p.subuNr x18, x20, x21
    li x19, 0x03980d70
    beq x18, x19, test171
    c.addi x15, 0x1
test171:
    li x18, 0xd8151a3e
    li x20, 0x7e6826a7
    li x21, 0x7c5f1d29
    p.subuNr x18, x20, x21
    li x19, 0x002cd679
    beq x18, x19, test172
    c.addi x15, 0x1
test172:
    li x18, 0x8669f154
    li x20, 0x5b4183ac
    li x21, 0x57bd7285
    p.subuNr x18, x20, x21
    li x19, 0x159436d
    beq x18, x19, test173
    c.addi x15, 0x1
test173:
    li x18, 0x523c0d99
    li x20, 0x3d395a21
    li x21, 0xd07290bc
    p.subuNr x18, x20, x21
    li x19, 0x00000001
    beq x18, x19, test174
    c.addi x15, 0x1
test174:
    li x18, 0x448a8dd2
    li x20, 0x0a108d00
    li x21, 0x660481a2
    p.subuNr x18, x20, x21
    li x19, 0x0e9e8034
    beq x18, x19, test175
    c.addi x15, 0x1
#tests175-180 test the p.subRNr instruction. values loaded in and compared to are expected output values
#p.subRNr instruction is of format "p.subRNr rD, rs1, rs2". rD = (rD - rs1 + 2^(rs2[4:0]-1)) >>> rs2[4:0]
test175:
    li x18, 0xb3940dbe
    li x20, 0x6d94e10e
    li x21, 0xfc9c1515
    p.subRNr x18, x20, x21
    li x19, 0x230
    beq x18, x19, test176
    c.addi x15, 0x1
test176:
    li x18, 0xe303c6ae
    li x20, 0x022bbb19
    li x21, 0xcb889d81
    p.subRNr x18, x20, x21
    li x19, 0xf06c05cb
    beq x18, x19, test177
    c.addi x15, 0x1
test177:
    li x18, 0xb838e0d6
    li x20, 0xbbc61816
    li x21, 0x642520d2
    p.subRNr x18, x20, x21
    li x19, 0xffffff1d
    beq x18, x19, test178
    c.addi x15, 0x1
test178:
    li x18, 0x43cb36c9
    li x20, 0x4307307c
    li x21, 0xd88202e7
    p.subRNr x18, x20, x21
    li x19, 0x0001880d
    beq x18, x19, test179
    c.addi x15, 0x1
test179:
    li x18, 0x46ccf70f
    li x20, 0x35be2580
    li x21, 0x23e1312f
    p.subRNr x18, x20, x21
    li x19, 0x0000221e
    beq x18, x19, test180
    c.addi x15, 0x1
test180:
    li x18, 0xdcfbbbc2
    li x20, 0xafc4a083
    li x21, 0xf4b525f8
    p.subRNr x18, x20, x21
    li x19, 0x0000002d
    beq x18, x19, test181
    c.addi x15, 0x1
#tests181-186 test the p.subuRNr instruction. values loaded in and compared to are expected output values
#p.subuRNr instruction is of format "p.subuRNr rD, rs1, rs2". rD = (rD - rs1 + 2^(rs2[4:0]-1)) >> rs2[4:0]
test181:
    li x18, 0xb3940dbe
    li x20, 0x6d94e10e
    li x21, 0xfc9c1515
    p.subuRNr x18, x20, x21
    li x19, 0x00000230
    beq x18, x19, test182
    c.addi x15, 0x1
test182:
    li x18, 0xe303c6ae
    li x20, 0x022bbb19
    li x21, 0xcb889d81
    p.subuRNr x18, x20, x21
    li x19, 0x706c05cb
    beq x18, x19, test183
    c.addi x15, 0x1
test183:
    li x18, 0xb838e0d6
    li x20, 0xbbc61816
    li x21, 0x642520d2
    p.subuRNr x18, x20, x21
    li x19, 0x00003f1d
    beq x18, x19, test184
    c.addi x15, 0x1
test184:
    li x18, 0x43cb36c9
    li x20, 0x4307307c
    li x21, 0xd88202e7
    p.subuRNr x18, x20, x21
    li x19, 0x0001880d
    beq x18, x19, test185
    c.addi x15, 0x1
test185:
    li x18, 0x46ccf70f
    li x20, 0x35be2580
    li x21, 0x23e1312f
    p.subuRNr x18, x20, x21
    li x19, 0x0000221e
    beq x18, x19, test186
    c.addi x15, 0x1
test186:
    li x18, 0xdcfbbbc2
    li x20, 0xafc4a083
    li x21, 0xf4b525f8
    p.subuRNr x18, x20, x21
    li x19, 0x0000002d
    beq x18, x19, exit_check
    c.addi x15, 0x1
exit_check:
    lw x18, test_results /* report result */
    beq x15, x0, exit
    li x18, 1
exit:
    li x17, 0x20000000
    sw x18,0(x17)
    wfi
