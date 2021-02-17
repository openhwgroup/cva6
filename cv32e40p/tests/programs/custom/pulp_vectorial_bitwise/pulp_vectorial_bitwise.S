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
#tests some vectorial/SIMD instructions. NOTE: value of register x15 at the end of the test is the error count
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
#tests1-6 test the pv.or.h instruction. values loaded in and compared to are expected output values
#pv.or.h is of the form "pv.or.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >> rs2[31:16], rD[15:0] = rs1[15:0] >> rs2[15:0]
test1:
    li x17, 0x657bda72
    li x18, 0x59aa04b1
    pv.or.h x19, x17, x18
    li x20, 0x7dfbdef3
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x140a6ff7
    li x18, 0x0efdd06b
    pv.or.h x19, x17, x18
    li x20, 0x1effffff
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0x9983f501
    li x18, 0x16f9d5f0
    pv.or.h x19, x17, x18
    li x20, 0x9ffbf5f1
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0xd92d92d6
    li x18, 0xbba807a1
    pv.or.h x19, x17, x18
    li x20, 0xfbad97f7
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0xc00e6d89
    li x18, 0xeed71ddf
    pv.or.h x19, x17, x18
    li x20, 0xeedf7ddf
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x1e395fc2
    li x18, 0xf69ecbd2
    pv.or.h x19, x17, x18
    li x20, 0xfebfdfd2
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.or.sc.h instruction. values loaded in and compared to are expected output values
#pv.or.sc.h is of the form "pv.or.sc.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >> rs2[15:0], rD[15:0] = rs1[15:0] >> rs2[15:0]
test7:
    li x17, 0x3fe3b0fa
    li x18, 0xb954f88c
    pv.or.sc.h x19, x17, x18
    li x20, 0xffeff8fe
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x662374b9
    li x18, 0xa607b208
    pv.or.sc.h x19, x17, x18
    li x20, 0xf62bf6b9
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x58deebb1
    li x18, 0xd8fc3c47
    pv.or.sc.h x19, x17, x18
    li x20, 0x7cdffff7
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0xecc73ceb
    li x18, 0x1412bcc9
    pv.or.sc.h x19, x17, x18
    li x20, 0xfccfbceb
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0x32580dc8
    li x18, 0x15072c8c
    pv.or.sc.h x19, x17, x18
    li x20, 0x3edc2dcc
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x4d38d066
    li x18, 0x89eb0164
    pv.or.sc.h x19, x17, x18
    li x20, 0x4d7cd166
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.or.sci.h instruction. values loaded in and compared to are expected output values
#pv.or.sci.h is of the form "pv.or.sci.h rD, rs1, Imm6". rD[31:16] = rs1[31:16] >> Imm6, rD[15:0] = rs1[15:0] >> Imm6
test13:
    li x17, 0x2d49a810
    pv.or.sci.h x19, x17, 0x1f
    li x20, 0x2d5fa81f
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0x45102ecd
    pv.or.sci.h x19, x17, 0x12
    li x20, 0x45122edf
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0x22c7ba55
    pv.or.sci.h x19, x17, 0x01
    li x20, 0x22c7ba55
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0xf573676d
    pv.or.sci.h x19, x17, 0x0e
    li x20, 0xf57f676f
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x1c8ca198
    pv.or.sci.h x19, x17, 0x08
    li x20, 0x1c8ca198
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x2b71cd21
    pv.or.sci.h x19, x17, 0x16
    li x20, 0x2b77cd37
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.or.b instruction. values loaded in and compared to are expected output values
#pv.or.b is of the form "pv.or.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >> rs2[31:24],
#rD[23:16] = rs1[23:16] >> rs2[23:16], rD[15:8] = rs1[15:8] >> rs2[15:8], rD[7:0] = rs1[7:0] >> rs2[7:0]
test19:
    li x17, 0xe0460e79
    li x18, 0xf9cbde58
    pv.or.b x19, x17, x18
    li x20, 0xf9cfde79
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0xe1b0d64f
    li x18, 0x49dc6980
    pv.or.b x19, x17, x18
    li x20, 0xe9fcffcf
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0xdcbf8a96
    li x18, 0x3864501b
    pv.or.b x19, x17, x18
    li x20, 0xfcffda9f
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0x0e7be150
    li x18, 0x23016c43
    pv.or.b x19, x17, x18
    li x20, 0x2f7bed53
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0x64da5da8
    li x18, 0xdc6f702e
    pv.or.b x19, x17, x18
    li x20, 0xfcff7dae
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0xbea51598
    li x18, 0x11ea3b21
    pv.or.b x19, x17, x18
    li x20, 0xbfef3fb9
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.or.sc.b instruction. values loaded in and compared to are expected output values
#pv.or.sc.b is of the form "pv.or.sc.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >> rs2[7:0],
#rD[23:16] = rs1[23:16] >> rs2[7:0], rD[15:8] = rs1[15:8] >> rs2[7:0], rD[7:0] = rs1[7:0] >> rs2[7:0]
test25:
    li x17, 0x9ecb68ba
    li x18, 0x92d5cc2f
    pv.or.sc.b x19, x17, x18
    li x20, 0xbfef6fbf
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x20f9e89d
    li x18, 0x5e977c24
    pv.or.sc.b x19, x17, x18
    li x20, 0x24fdecbd
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0x88e586ca
    li x18, 0xec9682ab
    pv.or.sc.b x19, x17, x18
    li x20, 0xabefafeb
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0x770be1de
    li x18, 0xfc975a74
    pv.or.sc.b x19, x17, x18
    li x20, 0x777ff5fe
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0x18c52e2c
    li x18, 0xd9fa93c4
    pv.or.sc.b x19, x17, x18
    li x20, 0xdcc5eeec
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0xfdc10da8
    li x18, 0xea8f828f
    pv.or.sc.b x19, x17, x18
    li x20, 0xffcf8faf
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.or.sci.b instruction. values loaded in and compared to are expected output values
#pv.or.sci.b is of the form "pv.or.sci.b rD, rs1, Imm6". rD[31:24] = rs1[31:24] >> Imm6,
#rD[23:16] = rs1[23:16] >> Imm6, rD[15:8] = rs1[15:8] >> Imm6, rD[7:0] = rs1[7:0] >> Imm6
test31:
    li x17, 0x45f2f26f
    pv.or.sci.b x19, x17, 0x01
    li x20, 0x45f3f36f
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0xef678ffe
    pv.or.sci.b x19, x17, 0x06
    li x20, 0xef678ffe
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0xa230117b
    pv.or.sci.b x19, x17, 0x1f
    li x20, 0xbf3f1f7f
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0xa0de4b63
    pv.or.sci.b x19, x17, 0x11
    li x20, 0xb1df5b73
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0xe28220ff
    pv.or.sci.b x19, x17, 0x1e
    li x20, 0xfe9e3eff
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0x03c56ba9
    pv.or.sci.b x19, x17, 0x0c
    li x20, 0x0fcd6fad
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.xor.h instruction. values loaded in and compared to are expected output values
#pv.xor.h is of the form "pv.xor.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >>> rs2[31:16], rD[15:0] = rs1[15:0] >>> rs2[15:0]
test37:
    li x17, 0x8d9067f6
    li x18, 0x348887b4
    pv.xor.h x19, x17, x18
    li x20, 0xb918e042
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0x7407dc4e
    li x18, 0xae5b3cc1
    pv.xor.h x19, x17, x18
    li x20, 0xda5ce08f
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0x4457727a
    li x18, 0x1ce7e477
    pv.xor.h x19, x17, x18
    li x20, 0x58b0960d
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x5796d5ce
    li x18, 0xb14e2f52
    pv.xor.h x19, x17, x18
    li x20, 0xe6d8fa9c
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0x2559bb33
    li x18, 0x9fb5165e
    pv.xor.h x19, x17, x18
    li x20, 0xbaecad6d
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0x1a4622f9
    li x18, 0x1cf98a38
    pv.xor.h x19, x17, x18
    li x20, 0x06bfa8c1
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.xor.sc.h instruction. values loaded in and compared to are expected output values
#pv.xor.sc.h is of the form "pv.xor.sc.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >>> rs2[15:0], rD[15:0] = rs1[15:0] >>> rs2[15:0]
test43:
    li x17, 0xcea6c78a
    li x18, 0x8cedce07
    pv.xor.sc.h x19, x17, x18
    li x20, 0x00a1098d
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0x7ab9f70d
    li x18, 0x6aaa0ae2
    pv.xor.sc.h x19, x17, x18
    li x20, 0x705bfdef
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0x1b1b150f
    li x18, 0xa3982de1
    pv.xor.sc.h x19, x17, x18
    li x20, 0x36fa38ee
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0x71120818
    li x18, 0xf43847a5
    pv.xor.sc.h x19, x17, x18
    li x20, 0x36b74fbd
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0xe4bb9393
    li x18, 0xc3c8c085
    pv.xor.sc.h x19, x17, x18
    li x20, 0x243e5316
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0x0c7367ae
    li x18, 0x48b8deff
    pv.xor.sc.h x19, x17, x18
    li x20, 0xd28cb951
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.xor.sci.h instruction. values loaded in and compared to are expected output values
#pv.xor.sci.h is of the form "pv.xor.sci.h rD, rs1, Imm6". rD[31:16] = rs1[31:16] >>> Imm6, rD[15:0] = rs1[15:0] >>> Imm6
test49:
    li x17, 0xc6a93f9a
    pv.xor.sci.h x19, x17, 0x0f
    li x20, 0xc6a63f95
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0xc072435e
    pv.xor.sci.h x19, x17, 0x14
    li x20, 0xc066434a
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0x3f0de36e
    pv.xor.sci.h x19, x17, 0x1c
    li x20, 0x3f11e372
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0x82d96782
    pv.xor.sci.h x19, x17, 0x17
    li x20, 0x82ce6795
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x602eae54
    pv.xor.sci.h x19, x17, 0x04
    li x20, 0x602aae50
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0xeef13cf5
    pv.xor.sci.h x19, x17, 0x0d
    li x20, 0xeefc3cf8
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.xor.b instruction. values loaded in and compared to are expected output values
#pv.xor.b is of the form "pv.xor.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >>> rs2[31:24],
#rD[23:16] = rs1[23:16] >>> rs2[23:16], rD[15:8] = rs1[15:8] >>> rs2[15:8], rD[7:0] = rs1[7:0] >>> rs2[7:0]
test55:
    li x17, 0x9d52faba
    li x18, 0x0e94d9d0
    pv.xor.b x19, x17, x18
    li x20, 0x93c6236a
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0xe23099b4
    li x18, 0xf941d6d5
    pv.xor.b x19, x17, x18
    li x20, 0x1b714f61
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0x5ecd0570
    li x18, 0xea32442c
    pv.xor.b x19, x17, x18
    li x20, 0xb4ff415c
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0x6e041a3f
    li x18, 0xe50b5b60
    pv.xor.b x19, x17, x18
    li x20, 0x8b0f415f
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0x2759fc4c
    li x18, 0xb0e789eb
    pv.xor.b x19, x17, x18
    li x20, 0x97be75a7
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0x4e17fbca
    li x18, 0x8c91bc4c
    pv.xor.b x19, x17, x18
    li x20, 0xc2864786
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.xor.sc.b instruction. values loaded in and compared to are expected output values
#pv.xor.sc.b is of the form "pv.xor.sc.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >>> rs2[7:0],
#rD[23:16] = rs1[23:16] >>> rs2[7:0], rD[15:8] = rs1[15:8] >>> rs2[7:0], rD[7:0] = rs1[7:0] >>> rs2[7:0]
test61:
    li x17, 0x9d8cd086
    li x18, 0x11b6edc7
    pv.xor.sc.b x19, x17, x18
    li x20, 0x5a4b1741
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x8656c5da
    li x18, 0xa0214b3c
    pv.xor.sc.b x19, x17, x18
    li x20, 0xba6af9e6
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0xb8647504
    li x18, 0x931f58ee
    pv.xor.sc.b x19, x17, x18
    li x20, 0x568a9bea
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0xa4f892a6
    li x18, 0xfeb834fd
    pv.xor.sc.b x19, x17, x18
    li x20, 0x59056f5b
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0x483d6346
    li x18, 0xfbcd9b8f
    pv.xor.sc.b x19, x17, x18
    li x20, 0xc7b2ecc9
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0x8ed5e422
    li x18, 0x9897d69d
    pv.xor.sc.b x19, x17, x18
    li x20, 0x134879bf
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.xor.sci.b instruction. values loaded in and compared to are expected output values
#pv.xor.sci.b is of the form "pv.xor.sci.b rD, rs1, Imm6". rD[31:24] = rs1[31:24] >>> Imm6,
#rD[23:16] = rs1[23:16] >>> Imm6, rD[15:8] = rs1[15:8] >>> Imm6, rD[7:0] = rs1[7:0] >>> Imm6
test67:
    li x17, 0x9e7e2c08
    pv.xor.sci.b x19, x17, 0x0c
    li x20, 0x92722004
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0x70f016c4
    pv.xor.sci.b x19, x17, 0x0f
    li x20, 0x7fff19cb
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0x31b52ee7
    pv.xor.sci.b x19, x17, 0x10
    li x20, 0x21a53ef7
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0xfdac3e79
    pv.xor.sci.b x19, x17, 0x11
    li x20, 0xecbd2f68
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0xe4f56f6b
    pv.xor.sci.b x19, x17, 0x07
    li x20, 0xe3f2686c
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0x385f4c51
    pv.xor.sci.b x19, x17, 0x19
    li x20, 0x21465548
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.and.h instruction. values loaded in and compared to are expected output values
#pv.and.h is of the form "pv.and.h rD, rs1, rs2". rD[31:16] = rs1[31:16] << rs2[31:16], rD[15:0] = rs1[15:0] << rs2[15:0]
test73:
    li x17, 0x579f4304
    li x18, 0xe1c62010
    pv.and.h x19, x17, x18
    li x20, 0x41860000
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x17, 0x9690792b
    li x18, 0x88ec0a3f
    pv.and.h x19, x17, x18
    li x20, 0x8080082b
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x17, 0x0b628f04
    li x18, 0xdfb558a2
    pv.and.h x19, x17, x18
    li x20, 0x0b200800
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x17, 0xdf5fb37d
    li x18, 0xa251556f
    pv.and.h x19, x17, x18
    li x20, 0x8251116d
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x17, 0x9dc1792b
    li x18, 0x93e4705f
    pv.and.h x19, x17, x18
    li x20, 0x91c0700b
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x17, 0xe30d8661
    li x18, 0x4b2737b3
    pv.and.h x19, x17, x18
    li x20, 0x43050621
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the pv.and.sc.h instruction. values loaded in and compared to are expected output values
#pv.and.sc.h is of the form "pv.and.sc.h rD, rs1, rs2". rD[31:16] = rs1[31:16] << rs2[15:0], rD[15:0] = rs1[15:0] << rs2[15:0]
test79:
    li x17, 0x272c6cee
    li x18, 0xab0fe7df
    pv.and.sc.h x19, x17, x18
    li x20, 0x270c64ce
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x17, 0x686af499
    li x18, 0x1d488f2d
    pv.and.sc.h x19, x17, x18
    li x20, 0x08288409
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x17, 0x10d98c7f
    li x18, 0x8dfa6d66
    pv.and.sc.h x19, x17, x18
    li x20, 0x00400c66
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x17, 0xde5ac9d8
    li x18, 0x6fe15777
    pv.and.sc.h x19, x17, x18
    li x20, 0x56524150
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x17, 0x6d5497ab
    li x18, 0x3695a0fb
    pv.and.sc.h x19, x17, x18
    li x20, 0x205080ab
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x17, 0x57db7990
    li x18, 0xe35c3a98
    pv.and.sc.h x19, x17, x18
    li x20, 0x12983890
    beq x20, x19, test85
    c.addi x15, 0x1
#tests85-90 test the pv.and.sci.h instruction. values loaded in and compared to are expected output values
#pv.and.sci.h is of the form "pv.and.sci.h rD, rs1, Imm6". rD[31:16] = rs1[31:16] << Imm6, rD[15:0] = rs1[15:0] << Imm6
test85:
    li x17, 0x6b5a90ee
    pv.and.sci.h x19, x17, 0x1c
    li x20, 0x0018000c
    beq x20, x19, test86
    c.addi x15, 0x1
test86:
    li x17, 0x4eed2f8c
    pv.and.sci.h x19, x17, 0x1f
    li x20, 0x000d000c
    beq x20, x19, test87
    c.addi x15, 0x1
test87:
    li x17, 0x2d79a92b
    pv.and.sci.h x19, x17, 0x04
    li x20, 0x00000000
    beq x20, x19, test88
    c.addi x15, 0x1
test88:
    li x17, 0x6dfdffe1
    pv.and.sci.h x19, x17, 0x05
    li x20, 0x00050001
    beq x20, x19, test89
    c.addi x15, 0x1
test89:
    li x17, 0x9219e929
    pv.and.sci.h x19, x17, 0x12
    li x20, 0x00100000
    beq x20, x19, test90
    c.addi x15, 0x1
test90:
    li x17, 0x4995fb0a
    pv.and.sci.h x19, x17, 0x0f
    li x20, 0x0005000a
    beq x20, x19, test91
    c.addi x15, 0x1
#tests91-96 test the pv.and.b instruction. values loaded in and compared to are expected output values
#pv.and.b is of the form "pv.and.b rD, rs1, rs2". rD[31:24] = rs1[31:24] << rs2[31:24],
#rD[23:16] = rs1[23:16] << rs2[23:16], rD[15:8] = rs1[15:8] << rs2[15:8], rD[7:0] = rs1[7:0] << rs2[7:0]
test91:
    li x17, 0x457241b2
    li x18, 0x5b9c16cc
    pv.and.b x19, x17, x18
    li x20, 0x41100080
    beq x20, x19, test92
    c.addi x15, 0x1
test92:
    li x17, 0xe15f82cb
    li x18, 0x8c82489e
    pv.and.b x19, x17, x18
    li x20, 0x8002008a
    beq x20, x19, test93
    c.addi x15, 0x1
test93:
    li x17, 0x7e41586d
    li x18, 0xf63a7d04
    pv.and.b x19, x17, x18
    li x20, 0x76005804
    beq x20, x19, test94
    c.addi x15, 0x1
test94:
    li x17, 0xb00fc96c
    li x18, 0x551491bb
    pv.and.b x19, x17, x18
    li x20, 0x10048128
    beq x20, x19, test95
    c.addi x15, 0x1
test95:
    li x17, 0x70e0222e
    li x18, 0xcf057cfe
    pv.and.b x19, x17, x18
    li x20, 0x4000202e
    beq x20, x19, test96
    c.addi x15, 0x1
test96:
    li x17, 0x85f019a2
    li x18, 0xbe5330d7
    pv.and.b x19, x17, x18
    li x20, 0x84501082
    beq x20, x19, test97
    c.addi x15, 0x1
#tests97-102 test the pv.and.sc.b instruction. values loaded in and compared to are expected output values
#pv.and.sc.b is of the form "pv.and.sc.b rD, rs1, rs2". rD[31:24] = rs1[31:24] << rs2[7:0],
#rD[23:16] = rs1[23:16] << rs2[7:0], rD[15:8] = rs1[15:8] << rs2[7:0], rD[7:0] = rs1[7:0] << rs2[7:0]
test97:
    li x17, 0x33e0da01
    li x18, 0x36639341
    pv.and.sc.b x19, x17, x18
    li x20, 0x01404001
    beq x20, x19, test98
    c.addi x15, 0x1
test98:
    li x17, 0x51ae5970
    li x18, 0x956799ea
    pv.and.sc.b x19, x17, x18
    li x20, 0x40aa4860
    beq x20, x19, test99
    c.addi x15, 0x1
test99:
    li x17, 0xa2dd188a
    li x18, 0x3713bafc
    pv.and.sc.b x19, x17, x18
    li x20, 0xa0dc1888
    beq x20, x19, test100
    c.addi x15, 0x1
test100:
    li x17, 0x134052e1
    li x18, 0x9dfe3aaa
    pv.and.sc.b x19, x17, x18
    li x20, 0x020002a0
    beq x20, x19, test101
    c.addi x15, 0x1
test101:
    li x17, 0xdfcf294a
    li x18, 0x12d2eba3
    pv.and.sc.b x19, x17, x18
    li x20, 0x83832102
    beq x20, x19, test102
    c.addi x15, 0x1
test102:
    li x17, 0x01c863a2
    li x18, 0x9ccd2e91
    pv.and.sc.b x19, x17, x18
    li x20, 0x01800180
    beq x20, x19, test103
    c.addi x15, 0x1
#tests103-108 test the pv.and.sci.b instruction. values loaded in and compared to are expected output values
#pv.and.sci.b is of the form "pv.and.sci.b rD, rs1, Imm6". rD[31:24] = rs1[31:24] << Imm6,
#rD[23:16] = rs1[23:16] << Imm6, rD[15:8] = rs1[15:8] << Imm6, rD[7:0] = rs1[7:0] << Imm6
test103:
    li x17, 0x72c32832
    pv.and.sci.b x19, x17, 0x0a
    li x20, 0x02020802
    beq x20, x19, test104
    c.addi x15, 0x1
test104:
    li x17, 0x31ee72ee
    pv.and.sci.b x19, x17, 0x1e
    li x20, 0x100e120e
    beq x20, x19, test105
    c.addi x15, 0x1
test105:
    li x17, 0x524e2d03
    pv.and.sci.b x19, x17, 0x16
    li x20, 0x12060402
    beq x20, x19, test106
    c.addi x15, 0x1
test106:
    li x17, 0x8689d89c
    pv.and.sci.b x19, x17, 0x0f
    li x20, 0x609080c
    beq x20, x19, test107
    c.addi x15, 0x1
test107:
    li x17, 0x89c2bfb1
    pv.and.sci.b x19, x17, 0x14
    li x20, 0x00001410
    beq x20, x19, test108
    c.addi x15, 0x1
test108:
    li x17, 0x5c2e4685
    pv.and.sci.b x19, x17, 0x1f
    li x20, 0x1c0e0605
    beq x20, x19, exit_check
    c.addi x15, 0x1
exit_check:
    lw x18, test_results /* report result */
    beq x15, x0, exit
    li x18, 1
exit:
    li x17, 0x20000000
    sw x18,0(x17)
    wfi
