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
#tests1-6 test the pv.cmpgtu.h instruction. values loaded in and compared to are expected output values
#pv.cmpgtu.h is of the form "pv.cmpgtu.h rD, rs1, rs2".
test1:
    li x17, 0x6013caa4
    li x18, 0xb14037d4
    pv.cmpgtu.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0xb0fd8577
    li x18, 0x3671504c
    pv.cmpgtu.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0xea7b84d3
    li x18, 0x8153fdc1
    pv.cmpgtu.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x9dc46f0c
    li x18, 0x15fe331b
    pv.cmpgtu.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0xf1d0377c
    li x18, 0xf7c5457c
    pv.cmpgtu.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0xc36186a9
    li x18, 0xb14c86a9
    pv.cmpgtu.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.cmpgtu.sc.h instruction. values loaded in and compared to are expected output values
#pv.cmpgtu.sc.h is of the form "pv.cmpgtu.sc.h rD, rs1, rs2".
test7:
    li x17, 0x00e7de9f
    li x18, 0x09e6feef
    pv.cmpgtu.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x69491061
    li x18, 0xc83201bc
    pv.cmpgtu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x00ac6630
    li x18, 0xcf0f0463
    pv.cmpgtu.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0x44b6d853
    li x18, 0x07a42247
    pv.cmpgtu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0xef1972e7
    li x18, 0xea98ed5f
    pv.cmpgtu.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x9f8cdd18
    li x18, 0xa7cf51c7
    pv.cmpgtu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.cmpgtu.sci.h instruction. values loaded in and compared to are expected output values
#pv.cmpgtu.sci.h is of the form "pv.cmpgtu.sci.h rD, rs1, Imm6".
test13:
    li x17, 0xcb843416
    pv.cmpgtu.sci.h x19, x17, 0x2
    li x20, 0xffffffff
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0x0008483b
    pv.cmpgtu.sci.h x19, x17, 0x8
    li x20, 0x0000ffff
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0x2c99000e
    pv.cmpgtu.sci.h x19, x17, 0xf
    li x20, 0xffff0000
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0xe871c0f9
    pv.cmpgtu.sci.h x19, x17, 0x5
    li x20, 0xffffffff
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x031b0c7b
    pv.cmpgtu.sci.h x19, x17, 0x0
    li x20, 0xffffffff
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x00000001
    pv.cmpgtu.sci.h x19, x17, 0x8
    li x20, 0x00000000
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.cmpgtu.b instruction. values loaded in and compared to are expected output values
#pv.cmpgtu.b is of the form "pv.cmpgtu.b rD, rs1, rs2".
test19:
    li x17, 0xf32d8965
    li x18, 0x467b9233
    pv.cmpgtu.b x19, x17, x18
    li x20, 0xff0000ff
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x99646fbb
    li x18, 0x3b1a545f
    pv.cmpgtu.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0xb4da0e27
    li x18, 0xe9950e0a
    pv.cmpgtu.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0x2dbb65f6
    li x18, 0x7e87737e
    pv.cmpgtu.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0xa5f2c84c
    li x18, 0x8f7686be
    pv.cmpgtu.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0x27888653
    li x18, 0x99b500df
    pv.cmpgtu.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.cmpgtu.sc.b instruction. values loaded in and compared to are expected output values
#pv.cmpgtu.sc.b is of the form "pv.cmpgtu.sc.b rD, rs1, rs2".
test25:
    li x17, 0xfbc50434
    li x18, 0xc34df4ec
    pv.cmpgtu.sc.b x19, x17, x18
    li x20, 0xff000000
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x782cba40
    li x18, 0xde6e3cba
    pv.cmpgtu.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0x48404297
    li x18, 0xfe1d2742
    pv.cmpgtu.sc.b x19, x17, x18
    li x20, 0xff0000ff
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0x7250b4b8
    li x18, 0x20e7680c
    pv.cmpgtu.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0x732d7316
    li x18, 0x9e09e7b8
    pv.cmpgtu.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0x3a835a5f
    li x18, 0x34b2f75b
    pv.cmpgtu.sc.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.cmpgtu.sci.b instruction. values loaded in and compared to are expected output values
#pv.cmpgtu.sci.b is of the form "pv.cmpgtu.sci.b rD, rs1, Imm6".
test31:
    li x17, 0xeffe076f
    pv.cmpgtu.sci.b x19, x17, 0x7
    li x20, 0xffff00ff
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0x689e057b
    pv.cmpgtu.sci.b x19, x17, 0x8
    li x20, 0xffff00ff
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0x2ca79f2d
    pv.cmpgtu.sci.b x19, x17, 0xa
    li x20, 0xffffffff
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0xf5189ed5
    pv.cmpgtu.sci.b x19, x17, 0x2
    li x20, 0xffffffff
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x19ed73b1
    pv.cmpgtu.sci.b x19, x17, 0xf
    li x20, 0xffffffff
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0x9617f9de
    pv.cmpgtu.sci.b x19, x17, 0x5
    li x20, 0xffffffff
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.cmpgeu.h instruction. values loaded in and compared to are expected output values
#pv.cmpgeu.h is of the form "pv.cmpgeu.h rD, rs1, rs2".
test37:
    li x17, 0x4e8e5ede
    li x18, 0xf270491c
    pv.cmpgeu.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0xe0f0c81d
    li x18, 0x033e973c
    pv.cmpgeu.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0x59d559f4
    li x18, 0xb53559f4
    pv.cmpgeu.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x821b12b6
    li x18, 0x783dce4b
    pv.cmpgeu.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0x75d9ce25
    li x18, 0x86004200
    pv.cmpgeu.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0x8aa5ca19
    li x18, 0x4ca3f661
    pv.cmpgeu.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.cmpgeu.sc.h instruction. values loaded in and compared to are expected output values
#pv.cmpgeu.sc.h is of the form "pv.cmpgeu.sc.h rD, rs1, rs2".
test43:
    li x17, 0x74cd038c
    li x18, 0xf98d9c81
    pv.cmpgeu.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0x9af6df85
    li x18, 0xafa4251a
    pv.cmpgeu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0xf4bd11e7
    li x18, 0x85ded011
    pv.cmpgeu.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0xfc8f3b8b
    li x18, 0x9cf9fc8f
    pv.cmpgeu.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0x89fa6f08
    li x18, 0x76a22964
    pv.cmpgeu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0x767b9f82
    li x18, 0x3cb5863f
    pv.cmpgeu.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.cmpgeu.sci.h instruction. values loaded in and compared to are expected output values
#pv.cmpgeu.sci.h is of the form "pv.cmpgeu.sci.h rD, rs1, Imm6".
test49:
    li x17, 0x0004429d
    pv.cmpgeu.sci.h x19, x17, 0x5
    li x20, 0x0000ffff
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0x52985b2e
    pv.cmpgeu.sci.h x19, x17, 0x0
    li x20, 0xffffffff
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0x79a34cf9
    pv.cmpgeu.sci.h x19, x17, 0x3
    li x20, 0xffffffff
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0x4ada0001
    pv.cmpgeu.sci.h x19, x17, 0xd
    li x20, 0xffff0000
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x5490c2f6
    pv.cmpgeu.sci.h x19, x17, 0x8
    li x20, 0xffffffff
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0xc40682b2
    pv.cmpgeu.sci.h x19, x17, 0x2
    li x20, 0xffffffff
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.cmpgeu.b instruction. values loaded in and compared to are expected output values
#pv.cmpgeu.b is of the form "pv.cmpgeu.b rD, rs1, rs2".
test55:
    li x17, 0xd72fb6a6
    li x18, 0xbb2f3bcc
    pv.cmpgeu.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0xd8bc2481
    li x18, 0x7ddedccf
    pv.cmpgeu.b x19, x17, x18
    li x20, 0xff000000
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0xe3297a2f
    li x18, 0xe0d00ffd
    pv.cmpgeu.b x19, x17, x18
    li x20, 0xff00ff00
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0x5f3aac83
    li x18, 0xd2bfcb78
    pv.cmpgeu.b x19, x17, x18
    li x20, 0x000000ff
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0x6aaeb3b9
    li x18, 0x16ea1ecd
    pv.cmpgeu.b x19, x17, x18
    li x20, 0xff00ff00
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0xd0cfaeb9
    li x18, 0xdd9aa444
    pv.cmpgeu.b x19, x17, x18
    li x20, 0x00ffffff
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.cmpgeu.sc.b instruction. values loaded in and compared to are expected output values
#pv.cmpgeu.sc.b is of the form "pv.cmpgeu.sc.b rD, rs1, rs2".
test61:
    li x17, 0x3f51997e
    li x18, 0xfb9218a4
    pv.cmpgeu.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x04134e9b
    li x18, 0x70865b05
    pv.cmpgeu.sc.b x19, x17, x18
    li x20, 0x00ffffff
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0xcfa73661
    li x18, 0x8be8dca7
    pv.cmpgeu.sc.b x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0x5c8ef9dd
    li x18, 0x307d5327
    pv.cmpgeu.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0x275d8c36
    li x18, 0x69fa33df
    pv.cmpgeu.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0x7d9f572a
    li x18, 0x38e79e9e
    pv.cmpgeu.sc.b x19, x17, x18
    li x20, 0x00ff0000
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.cmpgeu.sci.b instruction. values loaded in and compared to are expected output values
#pv.cmpgeu.sci.b is of the form "pv.cmpgeu.sci.b rD, rs1, Imm6".
test67:
    li x17, 0x50082a23
    pv.cmpgeu.sci.b x19, x17, 0xc
    li x20, 0xff00ffff
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0xa1495c0f
    pv.cmpgeu.sci.b x19, x17, 0xf
    li x20, 0xffffffff
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0x6a2d9791
    pv.cmpgeu.sci.b x19, x17, 0x7
    li x20, 0xffffffff
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x91cc0098
    pv.cmpgeu.sci.b x19, x17, 0x1
    li x20, 0xffff00ff
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0x94429491
    pv.cmpgeu.sci.b x19, x17, 0x4
    li x20, 0xffffffff
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0x8e4b041c
    pv.cmpgeu.sci.b x19, x17, 0xa
    li x20, 0xffff00ff
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.cmpltu.h instruction. values loaded in and compared to are expected output values
#pv.cmpltu.h is of the form "pv.cmpltu.h rD, rs1, rs2".
test73:
    li x17, 0x6d362f93
    li x18, 0x6a0e3bdc
    pv.cmpltu.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x17, 0x011afdcf
    li x18, 0x750856f3
    pv.cmpltu.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x17, 0x3a5d7e42
    li x18, 0xa7054756
    pv.cmpltu.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x17, 0x5c324cdf
    li x18, 0xd0d5021d
    pv.cmpltu.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x17, 0x8d47f02a
    li x18, 0x419e1060
    pv.cmpltu.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x17, 0x810913b1
    li x18, 0x8c22678e
    pv.cmpltu.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the pv.cmpltu.sc.h instruction. values loaded in and compared to are expected output values
#pv.cmpltu.sc.h is of the form "pv.cmpltu.sc.h rD, rs1, rs2".
test79:
    li x17, 0x840378a0
    li x18, 0x84031cf1
    pv.cmpltu.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x17, 0x5a143639
    li x18, 0x1d7cf65e
    pv.cmpltu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x17, 0x9035f996
    li x18, 0xe2321917
    pv.cmpltu.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x17, 0x472212ef
    li x18, 0x074d6855
    pv.cmpltu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x17, 0x2766c214
    li x18, 0x27d4c4a5
    pv.cmpltu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x17, 0x293c9e5b
    li x18, 0xf854a192
    pv.cmpltu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test85
    c.addi x15, 0x1
#tests85-90 test the pv.cmpltu.sci.h instruction. values loaded in and compared to are expected output values
#pv.cmpltu.sci.h is of the form "pv.cmpltu.sci.h rD, rs1, Imm6".
test85:
    li x17, 0x47882da2
    pv.cmpltu.sci.h x19, x17, 0x0
    li x20, 0x00000000
    beq x20, x19, test86
    c.addi x15, 0x1
test86:
    li x17, 0x50710007
    pv.cmpltu.sci.h x19, x17, 0x8
    li x20, 0x0000ffff
    beq x20, x19, test87
    c.addi x15, 0x1
test87:
    li x17, 0x00014925
    pv.cmpltu.sci.h x19, x17, 0x4
    li x20, 0xffff0000
    beq x20, x19, test88
    c.addi x15, 0x1
test88:
    li x17, 0xedf9f32a
    pv.cmpltu.sci.h x19, x17, 0x2
    li x20, 0x00000000
    beq x20, x19, test89
    c.addi x15, 0x1
test89:
    li x17, 0x00060002
    pv.cmpltu.sci.h x19, x17, 0x9
    li x20, 0xffffffff
    beq x20, x19, test90
    c.addi x15, 0x1
test90:
    li x17, 0x8307d78b
    pv.cmpltu.sci.h x19, x17, 0xc
    li x20, 0x00000000
    beq x20, x19, test91
    c.addi x15, 0x1
#tests91-96 test the pv.cmpltu.b instruction. values loaded in and compared to are expected output values
#pv.cmpltu.b is of the form "pv.cmpltu.b rD, rs1, rs2".
test91:
    li x17, 0x9cbc6cec
    li x18, 0xa404e17f
    pv.cmpltu.b x19, x17, x18
    li x20, 0xff00ff00
    beq x20, x19, test92
    c.addi x15, 0x1
test92:
    li x17, 0x3565128b
    li x18, 0x4c32a248
    pv.cmpltu.b x19, x17, x18
    li x20, 0xff00ff00
    beq x20, x19, test93
    c.addi x15, 0x1
test93:
    li x17, 0xd684fdbe
    li x18, 0x27706aa1
    pv.cmpltu.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test94
    c.addi x15, 0x1
test94:
    li x17, 0xf0f72813
    li x18, 0x0c122859
    pv.cmpltu.b x19, x17, x18
    li x20, 0x000000ff
    beq x20, x19, test95
    c.addi x15, 0x1
test95:
    li x17, 0x971b89fc
    li x18, 0xf73da7fd
    pv.cmpltu.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test96
    c.addi x15, 0x1
test96:
    li x17, 0x543d0cda
    li x18, 0x7e3eb612
    pv.cmpltu.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test97
    c.addi x15, 0x1
#tests97-102 test the pv.cmpltu.sc.b instruction. values loaded in and compared to are expected output values
#pv.cmpltu.sc.b is of the form "pv.cmpltu.sc.b rD, rs1, rs2".
test97:
    li x17, 0xfcf54290
    li x18, 0xbc31f858
    pv.cmpltu.sc.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test98
    c.addi x15, 0x1
test98:
    li x17, 0xc8419963
    li x18, 0xcf960f32
    pv.cmpltu.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test99
    c.addi x15, 0x1
test99:
    li x17, 0xca0857c9
    li x18, 0x8cb4cb62
    pv.cmpltu.sc.b x19, x17, x18
    li x20, 0x00ffff00
    beq x20, x19, test100
    c.addi x15, 0x1
test100:
    li x17, 0x45000095
    li x18, 0x1500b74d
    pv.cmpltu.sc.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test101
    c.addi x15, 0x1
test101:
    li x17, 0x4bc43321
    li x18, 0x3c6ec6e9
    pv.cmpltu.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test102
    c.addi x15, 0x1
test102:
    li x17, 0xd560a84a
    li x18, 0x87ffefa8
    pv.cmpltu.sc.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test103
    c.addi x15, 0x1
#tests103-108 test the pv.cmpltu.sci.b instruction. values loaded in and compared to are expected output values
#pv.cmpltu.sci.b is of the form "pv.cmpltu.sci.b rD, rs1, Imm6".
test103:
    li x17, 0x66ed230a
    pv.cmpltu.sci.b x19, x17, 0xa
    li x20, 0x00000000
    beq x20, x19, test104
    c.addi x15, 0x1
test104:
    li x17, 0xc70baab8
    pv.cmpltu.sci.b x19, x17, 0xc
    li x20, 0x00ff0000
    beq x20, x19, test105
    c.addi x15, 0x1
test105:
    li x17, 0x4381c243
    pv.cmpltu.sci.b x19, x17, 0xb
    li x20, 0x00000000
    beq x20, x19, test106
    c.addi x15, 0x1
test106:
    li x17, 0x01020304
    pv.cmpltu.sci.b x19, x17, 0x4
    li x20, 0xffffff00
    beq x20, x19, test107
    c.addi x15, 0x1
test107:
    li x17, 0x29cfb5ca
    pv.cmpltu.sci.b x19, x17, 0x9
    li x20, 0x00000000
    beq x20, x19, test108
    c.addi x15, 0x1
test108:
    li x17, 0xf68378aa
    pv.cmpltu.sci.b x19, x17, 0x2
    li x20, 0x00000000
    beq x20, x19, test109
    c.addi x15, 0x1
#tests109-114 test the pv.cmpleu.h instruction. values loaded in and compared to are expected output values
#pv.cmpleu.h is of the form "pv.cmpleu.h rD, rs1, rs2".
test109:
    li x17, 0xc7bd326f
    li x18, 0x7cb7bb41
    pv.cmpleu.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test110
    c.addi x15, 0x1
test110:
    li x17, 0xc9724571
    li x18, 0x0a882c3c
    pv.cmpleu.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test111
    c.addi x15, 0x1
test111:
    li x17, 0x620810a7
    li x18, 0x162b10a7
    pv.cmpleu.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test112
    c.addi x15, 0x1
test112:
    li x17, 0x24bcacf5
    li x18, 0x51d0d881
    pv.cmpleu.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test113
    c.addi x15, 0x1
test113:
    li x17, 0x7ad769ff
    li x18, 0x1d85c249
    pv.cmpleu.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test114
    c.addi x15, 0x1
test114:
    li x17, 0xf95b86db
    li x18, 0xa0ad37c1
    pv.cmpleu.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test115
    c.addi x15, 0x1
#tests115-120 test the pv.cmpleu.sc.h instruction. values loaded in and compared to are expected output values
#pv.cmpleu.sc.h is of the form "pv.cmpleu.sc.h rD, rs1, rs2".
test115:
    li x17, 0x46b0e3ad
    li x18, 0x3722189b
    pv.cmpleu.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test116
    c.addi x15, 0x1
test116:
    li x17, 0x119c9fc3
    li x18, 0x3a6a119c
    pv.cmpleu.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test117
    c.addi x15, 0x1
test117:
    li x17, 0xf42b80dd
    li x18, 0xb6f2f147
    pv.cmpleu.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test118
    c.addi x15, 0x1
test118:
    li x17, 0xa2118935
    li x18, 0x8105d093
    pv.cmpleu.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test119
    c.addi x15, 0x1
test119:
    li x17, 0xc9d50ecd
    li x18, 0x4c4b0488
    pv.cmpleu.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test120
    c.addi x15, 0x1
test120:
    li x17, 0x416b44a1
    li x18, 0xab40256e
    pv.cmpleu.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test121
    c.addi x15, 0x1
#tests121-126 test the pv.cmpleu.sci.h instruction. values loaded in and compared to are expected output values
#pv.cmpleu.sci.h is of the form "pv.cmpleu.sci.h rD, rs1, Imm6".
test121:
    li x17, 0x000b7df0
    pv.cmpleu.sci.h x19, x17, 0xc
    li x20, 0xffff0000
    beq x20, x19, test122
    c.addi x15, 0x1
test122:
    li x17, 0xff73c470
    pv.cmpleu.sci.h x19, x17, 0x3
    li x20, 0x00000000
    beq x20, x19, test123
    c.addi x15, 0x1
test123:
    li x17, 0x0003000c
    pv.cmpleu.sci.h x19, x17, 0xe
    li x20, 0xffffffff
    beq x20, x19, test124
    c.addi x15, 0x1
test124:
    li x17, 0xe028b943
    pv.cmpleu.sci.h x19, x17, 0x6
    li x20, 0x00000000
    beq x20, x19, test125
    c.addi x15, 0x1
test125:
    li x17, 0x62d37357
    pv.cmpleu.sci.h x19, x17, 0x2
    li x20, 0x00000000
    beq x20, x19, test126
    c.addi x15, 0x1
test126:
    li x17, 0x57ac0007
    pv.cmpleu.sci.h x19, x17, 0x8
    li x20, 0x0000ffff
    beq x20, x19, test127
    c.addi x15, 0x1
#tests127-132 test the pv.cmpleu.b instruction. values loaded in and compared to are expected output values
#pv.cmpleu.b is of the form "pv.cmpleu.b rD, rs1, rs2".
test127:
    li x17, 0xdf0b0723
    li x18, 0xf61fa987
    pv.cmpleu.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test128
    c.addi x15, 0x1
test128:
    li x17, 0x40592630
    li x18, 0xa6ce9028
    pv.cmpleu.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test129
    c.addi x15, 0x1
test129:
    li x17, 0x47b64c62
    li x18, 0x1f94d351
    pv.cmpleu.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test130
    c.addi x15, 0x1
test130:
    li x17, 0xf2d4ec55
    li x18, 0xf51236ec
    pv.cmpleu.b x19, x17, x18
    li x20, 0xff0000ff
    beq x20, x19, test131
    c.addi x15, 0x1
test131:
    li x17, 0xfde2d521
    li x18, 0x73dd9821
    pv.cmpleu.b x19, x17, x18
    li x20, 0x000000ff
    beq x20, x19, test132
    c.addi x15, 0x1
test132:
    li x17, 0x659f8ad6
    li x18, 0x0bdf09f2
    pv.cmpleu.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test133
    c.addi x15, 0x1
#tests133-138 test the pv.cmpleu.sc.b instruction. values loaded in and compared to are expected output values
#pv.cmpleu.sc.b is of the form "pv.cmpleu.sc.b rD, rs1, rs2".
test133:
    li x17, 0x8d4458a6
    li x18, 0xa64e68ff
    pv.cmpleu.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test134
    c.addi x15, 0x1
test134:
    li x17, 0x94a65e59
    li x18, 0xd2cff673
    pv.cmpleu.sc.b x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test135
    c.addi x15, 0x1
test135:
    li x17, 0x73c213c3
    li x18, 0x61d4dcc2
    pv.cmpleu.sc.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test136
    c.addi x15, 0x1
test136:
    li x17, 0x513de5e5
    li x18, 0xa0c0e7b4
    pv.cmpleu.sc.b x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test137
    c.addi x15, 0x1
test137:
    li x17, 0xac520936
    li x18, 0x284c69f1
    pv.cmpleu.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test138
    c.addi x15, 0x1
test138:
    li x17, 0xe1e01123
    li x18, 0x28e067d8
    pv.cmpleu.sc.b x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test139
    c.addi x15, 0x1
#tests139-144 test the pv.cmpleu.sci.b instruction. values loaded in and compared to are expected output values
#pv.cmpleu.sci.b is of the form "pv.cmpleu.sci.b rD, rs1, Imm6".
test139:
    li x17, 0x43c87702
    pv.cmpleu.sci.b x19, x17, 0x9
    li x20, 0x000000ff
    beq x20, x19, test140
    c.addi x15, 0x1
test140:
    li x17, 0x02f755a9
    pv.cmpleu.sci.b x19, x17, 0x2
    li x20, 0xff000000
    beq x20, x19, test141
    c.addi x15, 0x1
test141:
    li x17, 0x0bb3103a
    pv.cmpleu.sci.b x19, x17, 0xc
    li x20, 0xff000000
    beq x20, x19, test142
    c.addi x15, 0x1
test142:
    li x17, 0x050e693e
    pv.cmpleu.sci.b x19, x17, 0xf
    li x20, 0xffff0000
    beq x20, x19, test143
    c.addi x15, 0x1
test143:
    li x17, 0x445ee72f
    pv.cmpleu.sci.b x19, x17, 0x3
    li x20, 0x00000000
    beq x20, x19, test144
    c.addi x15, 0x1
test144:
    li x17, 0x0f841e08
    pv.cmpleu.sci.b x19, x17, 0x8
    li x20, 0x000000ff
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
