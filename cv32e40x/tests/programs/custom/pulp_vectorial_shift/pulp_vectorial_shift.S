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
#tests1-6 test the pv.srl.h instruction. values loaded in and compared to are expected output values
#pv.srl.h is of the form "pv.srl.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >> rs2[31:16], rD[15:0] = rs1[15:0] >> rs2[15:0]
test1:
    li x17, 0xe127d500
    li x18, 0x000a0003
    pv.srl.h x19, x17, x18
    li x20, 0x00381aa0
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x50ef49de
    li x18, 0x000e000b
    pv.srl.h x19, x17, x18
    li x20, 0x00010009
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0x9c24b7e7
    li x18, 0x0002000c
    pv.srl.h x19, x17, x18
    li x20, 0x2709000b
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x9f21bbd4
    li x18, 0x0003000b
    pv.srl.h x19, x17, x18
    li x20, 0x13e40017
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0x28e2b8f4
    li x18, 0x000e0005
    pv.srl.h x19, x17, x18
    li x20, 0x000005c7
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x859f9138
    li x18, 0x000f0001
    pv.srl.h x19, x17, x18
    li x20, 0x0001489c
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.srl.sc.h instruction. values loaded in and compared to are expected output values
#pv.srl.sc.h is of the form "pv.srl.sc.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >> rs2[15:0], rD[15:0] = rs1[15:0] >> rs2[15:0]
test7:
    li x17, 0xb2555556
    li x18, 0x18040003
    pv.srl.sc.h x19, x17, x18
    li x20, 0x164a0aaa
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x386221dd
    li x18, 0x160e000c
    pv.srl.sc.h x19, x17, x18
    li x20, 0x00030002
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x809e5f46
    li x18, 0xf20c0006
    pv.srl.sc.h x19, x17, x18
    li x20, 0x0202017d
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0xaa5ca38a
    li x18, 0xc684000f
    pv.srl.sc.h x19, x17, x18
    li x20, 0x00010001
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0xd65e1061
    li x18, 0xc981000b
    pv.srl.sc.h x19, x17, x18
    li x20, 0x001a0002
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x9a4bb8e6
    li x18, 0x3e470001
    pv.srl.sc.h x19, x17, x18
    li x20, 0x4d255c73
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.srl.sci.h instruction. values loaded in and compared to are expected output values
#pv.srl.sci.h is of the form "pv.srl.sci.h rD, rs1, Imm6". rD[31:16] = rs1[31:16] >> Imm6, rD[15:0] = rs1[15:0] >> Imm6
test13:
    li x17, 0xcec0bdb9
    pv.srl.sci.h x19, x17, 0x5
    li x20, 0x067605ed
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0x3f62b493
    pv.srl.sci.h x19, x17, 0x2
    li x20, 0x0fd82d24
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0xd4b564d6
    pv.srl.sci.h x19, x17, 0x8
    li x20, 0x00d40064
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0x4a83c696
    pv.srl.sci.h x19, x17, 0x4
    li x20, 0x04a80c69
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x9c823245
    pv.srl.sci.h x19, x17, 0x5
    li x20, 0x04e40192
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x7315d811
    pv.srl.sci.h x19, x17, 0x1
    li x20, 0x398a6c08
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.srl.b instruction. values loaded in and compared to are expected output values
#pv.srl.b is of the form "pv.srl.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >> rs2[31:24],
#rD[23:16] = rs1[23:16] >> rs2[23:16], rD[15:8] = rs1[15:8] >> rs2[15:8], rD[7:0] = rs1[7:0] >> rs2[7:0]
test19:
    li x17, 0xcb831d7c
    li x18, 0x01060104
    pv.srl.b x19, x17, x18
    li x20, 0x65020e07
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x4a7ff967
    li x18, 0x02060507
    pv.srl.b x19, x17, x18
    li x20, 0x12010700
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0xaab480fe
    li x18, 0x05050703
    pv.srl.b x19, x17, x18
    li x20, 0x0505011f
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0x64f68a08
    li x18, 0x01000507
    pv.srl.b x19, x17, x18
    li x20, 0x32f60400
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0xa71763f2
    li x18, 0x02050301
    pv.srl.b x19, x17, x18
    li x20, 0x29000c79
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0xce4ce609
    li x18, 0x00040001
    pv.srl.b x19, x17, x18
    li x20, 0xce04e604
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.srl.sc.b instruction. values loaded in and compared to are expected output values
#pv.srl.sc.b is of the form "pv.srl.sc.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >> rs2[7:0],
#rD[23:16] = rs1[23:16] >> rs2[7:0], rD[15:8] = rs1[15:8] >> rs2[7:0], rD[7:0] = rs1[7:0] >> rs2[7:0]
test25:
    li x17, 0x0e62b9ac
    li x18, 0x42d80203
    pv.srl.sc.b x19, x17, x18
    li x20, 0x010c1715
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x1e8be092
    li x18, 0xbe676f07
    pv.srl.sc.b x19, x17, x18
    li x20, 0x00010101
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0xf0e9ab5a
    li x18, 0x881ac505
    pv.srl.sc.b x19, x17, x18
    li x20, 0x07070502
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0x3704ae00
    li x18, 0xad4d9f01
    pv.srl.sc.b x19, x17, x18
    li x20, 0x1b025700
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0x111237e9
    li x18, 0xe5232d06
    pv.srl.sc.b x19, x17, x18
    li x20, 0x00000003
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0x85bd0af6
    li x18, 0x730b0506
    pv.srl.sc.b x19, x17, x18
    li x20, 0x02020003
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.srl.sci.b instruction. values loaded in and compared to are expected output values
#pv.srl.sci.b is of the form "pv.srl.sci.b rD, rs1, Imm6". rD[31:24] = rs1[31:24] >> Imm6,
#rD[23:16] = rs1[23:16] >> Imm6, rD[15:8] = rs1[15:8] >> Imm6, rD[7:0] = rs1[7:0] >> Imm6
test31:
    li x17, 0x829e30a9
    pv.srl.sci.b x19, x17, 0x1
    li x20, 0x414f1854
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0x92338f86
    pv.srl.sci.b x19, x17, 0x5
    li x20, 0x04010404
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0xc03229a6
    pv.srl.sci.b x19, x17, 0x6
    li x20, 0x03000002
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0xf87ef97a
    pv.srl.sci.b x19, x17, 0x4
    li x20, 0x0f070f07
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x6873a284
    pv.srl.sci.b x19, x17, 0x7
    li x20, 0x00000101
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0xbe151d06
    pv.srl.sci.b x19, x17, 0x2
    li x20, 0x2f050701
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.sra.h instruction. values loaded in and compared to are expected output values
#pv.sra.h is of the form "pv.sra.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >>> rs2[31:16], rD[15:0] = rs1[15:0] >>> rs2[15:0]
test37:
    li x17, 0x6cc801e8
    li x18, 0x000f0005
    pv.sra.h x19, x17, x18
    li x20, 0x0000000f
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0xf984409a
    li x18, 0x00050004
    pv.sra.h x19, x17, x18
    li x20, 0xffcc0409
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0x8b7b2815
    li x18, 0x00060003
    pv.sra.h x19, x17, x18
    li x20, 0xfe2d0502
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x6a2c3d33
    li x18, 0x000b000c
    pv.sra.h x19, x17, x18
    li x20, 0x000d0003
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0x3e5e4ccd
    li x18, 0x00090001
    pv.sra.h x19, x17, x18
    li x20, 0x001f2666
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0x79a7027f
    li x18, 0x0007000d
    pv.sra.h x19, x17, x18
    li x20, 0x00f30000
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.sra.sc.h instruction. values loaded in and compared to are expected output values
#pv.sra.sc.h is of the form "pv.sra.sc.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >>> rs2[15:0], rD[15:0] = rs1[15:0] >>> rs2[15:0]
test43:
    li x17, 0x8d34283b
    li x18, 0x6796000c
    pv.sra.sc.h x19, x17, x18
    li x20, 0xfff80002
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0x112fe766
    li x18, 0x8b27000d
    pv.sra.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0xe0887dc1
    li x18, 0x347c000b
    pv.sra.sc.h x19, x17, x18
    li x20, 0xfffc000f
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0xb3b07b10
    li x18, 0x347c0006
    pv.sra.sc.h x19, x17, x18
    li x20, 0xfece01ec
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0xe7f042b4
    li x18, 0x592b0007
    pv.sra.sc.h x19, x17, x18
    li x20, 0xffcf0085
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0xc234a4b1
    li x18, 0xe80f0004
    pv.sra.sc.h x19, x17, x18
    li x20, 0xfc23fa4b
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.sra.sci.h instruction. values loaded in and compared to are expected output values
#pv.sra.sci.h is of the form "pv.sra.sci.h rD, rs1, Imm6". rD[31:16] = rs1[31:16] >>> Imm6, rD[15:0] = rs1[15:0] >>> Imm6
test49:
    li x17, 0x4af9a865
    pv.sra.sci.h x19, x17, 0x0
    li x20, 0x4af9a865
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0xe9370e0e
    pv.sra.sci.h x19, x17, 0xe
    li x20, 0xffff0000
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0x586aeefb
    pv.sra.sci.h x19, x17, 0x4
    li x20, 0x0586feef
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0xa5aa7ed3
    pv.sra.sci.h x19, x17, 0xa
    li x20, 0xffe9001f
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x39423068
    pv.sra.sci.h x19, x17, 0x3
    li x20, 0x0728060d
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0x1c371395
    pv.sra.sci.h x19, x17, 0x9
    li x20, 0x000e0009
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.sra.b instruction. values loaded in and compared to are expected output values
#pv.sra.b is of the form "pv.sra.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >>> rs2[31:24],
#rD[23:16] = rs1[23:16] >>> rs2[23:16], rD[15:8] = rs1[15:8] >>> rs2[15:8], rD[7:0] = rs1[7:0] >>> rs2[7:0]
test55:
    li x17, 0x8cbe613d
    li x18, 0x00040706
    pv.sra.b x19, x17, x18
    li x20, 0x8cfb0000
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0xae2831ce
    li x18, 0x02000104
    pv.sra.b x19, x17, x18
    li x20, 0xeb2818fc
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0xa49d1848
    li x18, 0x02070305
    pv.sra.b x19, x17, x18
    li x20, 0xe9ff0302
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0xf738b790
    li x18, 0x03000407
    pv.sra.b x19, x17, x18
    li x20, 0xfe38fbff
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0x5e99bd85
    li x18, 0x02060405
    pv.sra.b x19, x17, x18
    li x20, 0x17fefbfc
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0xcdbca023
    li x18, 0x02060504
    pv.sra.b x19, x17, x18
    li x20, 0xf3fefd02
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.sra.sc.b instruction. values loaded in and compared to are expected output values
#pv.sra.sc.b is of the form "pv.sra.sc.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >>> rs2[7:0],
#rD[23:16] = rs1[23:16] >>> rs2[7:0], rD[15:8] = rs1[15:8] >>> rs2[7:0], rD[7:0] = rs1[7:0] >>> rs2[7:0]
test61:
    li x17, 0xad972df0
    li x18, 0x05040006
    pv.sra.sc.b x19, x17, x18
    li x20, 0xfefe00ff
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0xfd535dbe
    li x18, 0x06030401
    pv.sra.sc.b x19, x17, x18
    li x20, 0xfe292edf
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0x81e96979
    li x18, 0x06030704
    pv.sra.sc.b x19, x17, x18
    li x20, 0xf8fe0607
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0xa54e5e43
    li x18, 0x03040502
    pv.sra.sc.b x19, x17, x18
    li x20, 0xe9131710
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0xcbf79c3b
    li x18, 0x04030106
    pv.sra.sc.b x19, x17, x18
    li x20, 0xfffffe00
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0x4e96f377
    li x18, 0x02070006
    pv.sra.sc.b x19, x17, x18
    li x20, 0x01feff01
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.sra.sci.b instruction. values loaded in and compared to are expected output values
#pv.sra.sci.b is of the form "pv.sra.sci.b rD, rs1, Imm6". rD[31:24] = rs1[31:24] >>> Imm6,
#rD[23:16] = rs1[23:16] >>> Imm6, rD[15:8] = rs1[15:8] >>> Imm6, rD[7:0] = rs1[7:0] >>> Imm6
test67:
    li x17, 0x42ba88d1
    pv.sra.sci.b x19, x17, 0x3
    li x20, 0x08f7f1fa
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0x3f70269e
    pv.sra.sci.b x19, x17, 0x2
    li x20, 0x0f1c09e7
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0xdd2e40ac
    pv.sra.sci.b x19, x17, 0x4
    li x20, 0xfd0204fa
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x68a0e6c0
    pv.sra.sci.b x19, x17, 0x7
    li x20, 0x00ffffff
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0x5b1cb2b7
    pv.sra.sci.b x19, x17, 0x0
    li x20, 0x5b1cb2b7
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0xaf4da78a
    pv.sra.sci.b x19, x17, 0x6
    li x20, 0xfe01fefe
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.sll.h instruction. values loaded in and compared to are expected output values
#pv.sll.h is of the form "pv.sll.h rD, rs1, rs2". rD[31:16] = rs1[31:16] << rs2[31:16], rD[15:0] = rs1[15:0] << rs2[15:0]
test73:
    li x17, 0x10a74307
    li x18, 0x00010008
    pv.sll.h x19, x17, x18
    li x20, 0x214e0700
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x17, 0xbba83884
    li x18, 0x000d0005
    pv.sll.h x19, x17, x18
    li x20, 0x00001080
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x17, 0x6e812011
    li x18, 0x000f000b
    pv.sll.h x19, x17, x18
    li x20, 0x80008800
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x17, 0xbdf5de4a
    li x18, 0x00050001
    pv.sll.h x19, x17, x18
    li x20, 0xbea0bc94
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x17, 0xc8c71be7
    li x18, 0x000c000c
    pv.sll.h x19, x17, x18
    li x20, 0x70007000
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x17, 0x0ef5fbe8
    li x18, 0x00010000
    pv.sll.h x19, x17, x18
    li x20, 0x1deafbe8
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the pv.sll.sc.h instruction. values loaded in and compared to are expected output values
#pv.sll.sc.h is of the form "pv.sll.sc.h rD, rs1, rs2". rD[31:16] = rs1[31:16] << rs2[15:0], rD[15:0] = rs1[15:0] << rs2[15:0]
test79:
    li x17, 0xea4b73f2
    li x18, 0xfc000003
    pv.sll.sc.h x19, x17, x18
    li x20, 0x52589f90
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x17, 0x50bae067
    li x18, 0x56d70009
    pv.sll.sc.h x19, x17, x18
    li x20, 0x7400ce00
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x17, 0x3a1f90a1
    li x18, 0x2671000b
    pv.sll.sc.h x19, x17, x18
    li x20, 0xf8000800
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x17, 0xb5580729
    li x18, 0x3c9f000c
    pv.sll.sc.h x19, x17, x18
    li x20, 0x80009000
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x17, 0xdf1cae90
    li x18, 0x468c0006
    pv.sll.sc.h x19, x17, x18
    li x20, 0xc700a400
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x17, 0x12550e34
    li x18, 0x57900008
    pv.sll.sc.h x19, x17, x18
    li x20, 0x55003400
    beq x20, x19, test85
    c.addi x15, 0x1
#tests85-90 test the pv.sll.sci.h instruction. values loaded in and compared to are expected output values
#pv.sll.sci.h is of the form "pv.sll.sci.h rD, rs1, Imm6". rD[31:16] = rs1[31:16] << Imm6, rD[15:0] = rs1[15:0] << Imm6
test85:
    li x17, 0xf896c991
    pv.sll.sci.h x19, x17, 0x7
    li x20, 0x4b00c880
    beq x20, x19, test86
    c.addi x15, 0x1
test86:
    li x17, 0xfac5bd85
    pv.sll.sci.h x19, x17, 0x9
    li x20, 0x8a000a00
    beq x20, x19, test87
    c.addi x15, 0x1
test87:
    li x17, 0x61812809
    pv.sll.sci.h x19, x17, 0x0
    li x20, 0x61812809
    beq x20, x19, test88
    c.addi x15, 0x1
test88:
    li x17, 0xab1f59ab
    pv.sll.sci.h x19, x17, 0xb
    li x20, 0xf8005800
    beq x20, x19, test89
    c.addi x15, 0x1
test89:
    li x17, 0xf3b53fd6
    pv.sll.sci.h x19, x17, 0x4
    li x20, 0x3b50fd60
    beq x20, x19, test90
    c.addi x15, 0x1
test90:
    li x17, 0x2bb960ef
    pv.sll.sci.h x19, x17, 0xc
    li x20, 0x9000f000
    beq x20, x19, test91
    c.addi x15, 0x1
#tests91-96 test the pv.sll.b instruction. values loaded in and compared to are expected output values
#pv.sll.b is of the form "pv.sll.b rD, rs1, rs2". rD[31:24] = rs1[31:24] << rs2[31:24],
#rD[23:16] = rs1[23:16] << rs2[23:16], rD[15:8] = rs1[15:8] << rs2[15:8], rD[7:0] = rs1[7:0] << rs2[7:0]
test91:
    li x17, 0x6d288d59
    li x18, 0x02030501
    pv.sll.b x19, x17, x18
    li x20, 0xb440a0b2
    beq x20, x19, test92
    c.addi x15, 0x1
test92:
    li x17, 0x33714b3c
    li x18, 0x06000303
    pv.sll.b x19, x17, x18
    li x20, 0xc07158e0
    beq x20, x19, test93
    c.addi x15, 0x1
test93:
    li x17, 0xd555d6d6
    li x18, 0x07060400
    pv.sll.b x19, x17, x18
    li x20, 0x804060d6
    beq x20, x19, test94
    c.addi x15, 0x1
test94:
    li x17, 0x486a2333
    li x18, 0x03040205
    pv.sll.b x19, x17, x18
    li x20, 0x40a08c60
    beq x20, x19, test95
    c.addi x15, 0x1
test95:
    li x17, 0x32a8546f
    li x18, 0x04060302
    pv.sll.b x19, x17, x18
    li x20, 0x2000a0bc
    beq x20, x19, test96
    c.addi x15, 0x1
test96:
    li x17, 0x4884d67f
    li x18, 0x07010105
    pv.sll.b x19, x17, x18
    li x20, 0x0008ace0
    beq x20, x19, test97
    c.addi x15, 0x1
#tests97-102 test the pv.sll.sc.b instruction. values loaded in and compared to are expected output values
#pv.sll.sc.b is of the form "pv.sll.sc.b rD, rs1, rs2". rD[31:24] = rs1[31:24] << rs2[7:0],
#rD[23:16] = rs1[23:16] << rs2[7:0], rD[15:8] = rs1[15:8] << rs2[7:0], rD[7:0] = rs1[7:0] << rs2[7:0]
test97:
    li x17, 0x00f117bc
    li x18, 0xad83d903
    pv.sll.sc.b x19, x17, x18
    li x20, 0x0088b8e0
    beq x20, x19, test98
    c.addi x15, 0x1
test98:
    li x17, 0xa10f69e0
    li x18, 0x2451e707
    pv.sll.sc.b x19, x17, x18
    li x20, 0x80808000
    beq x20, x19, test99
    c.addi x15, 0x1
test99:
    li x17, 0xfda54148
    li x18, 0xa82a0f06
    pv.sll.sc.b x19, x17, x18
    li x20, 0x40404000
    beq x20, x19, test100
    c.addi x15, 0x1
test100:
    li x17, 0xfa148144
    li x18, 0x67205504
    pv.sll.sc.b x19, x17, x18
    li x20, 0xa0401040
    beq x20, x19, test101
    c.addi x15, 0x1
test101:
    li x17, 0x0423ea84
    li x18, 0x73156305
    pv.sll.sc.b x19, x17, x18
    li x20, 0x80604080
    beq x20, x19, test102
    c.addi x15, 0x1
test102:
    li x17, 0x509b57b0
    li x18, 0x4de56401
    pv.sll.sc.b x19, x17, x18
    li x20, 0xa036ae60
    beq x20, x19, test103
    c.addi x15, 0x1
#tests103-108 test the pv.sll.sci.b instruction. values loaded in and compared to are expected output values
#pv.sll.sci.b is of the form "pv.sll.sci.b rD, rs1, Imm6". rD[31:24] = rs1[31:24] << Imm6,
#rD[23:16] = rs1[23:16] << Imm6, rD[15:8] = rs1[15:8] << Imm6, rD[7:0] = rs1[7:0] << Imm6
test103:
    li x17, 0x99de05f3
    pv.sll.sci.b x19, x17, 0x7
    li x20, 0x80008080
    beq x20, x19, test104
    c.addi x15, 0x1
test104:
    li x17, 0xac20afb7
    pv.sll.sci.b x19, x17, 0x5
    li x20, 0x8000e0e0
    beq x20, x19, test105
    c.addi x15, 0x1
test105:
    li x17, 0x252a0327
    pv.sll.sci.b x19, x17, 0x4
    li x20, 0x50a03070
    beq x20, x19, test106
    c.addi x15, 0x1
test106:
    li x17, 0x4dddd53d
    pv.sll.sci.b x19, x17, 0x0
    li x20, 0x4dddd53d
    beq x20, x19, test107
    c.addi x15, 0x1
test107:
    li x17, 0xca054618
    pv.sll.sci.b x19, x17, 0x1
    li x20, 0x940a8c30
    beq x20, x19, test108
    c.addi x15, 0x1
test108:
    li x17, 0x3088abde
    pv.sll.sci.b x19, x17, 0x3
    li x20, 0x804058f0
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
