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
#tests1-6 test the pv.dotup.h instruction. values loaded in and compared to are expected output values
#pv.dotup.h is of the form "pv.dotup.h rD, rs1, rs2"
test1:
    li x17, 0x8d7fd0d4
    li x18, 0xfc7b09b2
    pv.dotup.h x19, x17, x18
    li x20, 0x9375a76d
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x30794165
    li x18, 0x746b2820
    pv.dotup.h x19, x17, x18
    li x20, 0x204b0b33
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0xd3b7e82c
    li x18, 0x095ccaf7
    pv.dotup.h x19, x17, x18
    li x20, 0xbfd03f38
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x8147d144
    li x18, 0x6f633d3a
    pv.dotup.h x19, x17, x18
    li x20, 0x6a4c64dd
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0xd264baa9
    li x18, 0x40f0b913
    pv.dotup.h x19, x17, x18
    li x20, 0xbc50394b
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x9e2d2f27
    li x18, 0xa14bf1a7
    pv.dotup.h x19, x17, x18
    li x20, 0x902b1da0
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.dotup.sc.h instruction. values loaded in and compared to are expected output values
#pv.dotup.sc.h is of the form "pv.dotup.sc.h rD, rs1, rs2"
test7:
    li x17, 0x7850ff4b
    li x18, 0xf74314d0
    pv.dotup.sc.h x19, x17, x18
    li x20, 0x1e8949f0
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0xeed2cf26
    li x18, 0x4e449958
    pv.dotup.sc.h x19, x17, x18
    li x20, 0x0b228540
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x99c5cb0c
    li x18, 0x602feda7
    pv.dotup.sc.h x19, x17, x18
    li x20, 0x4b3e4157
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0x76f60132
    li x18, 0xfb3365f7
    pv.dotup.sc.h x19, x17, x18
    li x20, 0x2fdbb698
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0x9f2bae05
    li x18, 0xe194c218
    pv.dotup.sc.h x19, x17, x18
    li x20, 0xfc9d9c80
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0xa1e360b5
    li x18, 0xbd1db2ec
    pv.dotup.sc.h x19, x17, x18
    li x20, 0xb4bc1420
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.dotup.sci.h instruction. values loaded in and compared to are expected output values
#pv.dotup.sci.h is of the form "pv.dotup.sci.h rD, rs1, Imm6"
test13:
    li x17, 0xc30a2b68
    pv.dotup.sci.h x19, x17, 0x1f
    li x20, 0x001cdfce
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0x96437fa8
    pv.dotup.sci.h x19, x17, 0x04
    li x20, 0x000457ac
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0x0eba82f5
    pv.dotup.sci.h x19, x17, 0x1d
    li x20, 0x001080d3
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0xf8069c7d
    pv.dotup.sci.h x19, x17, 0x08
    li x20, 0x000ca418
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x8dff2c6d
    pv.dotup.sci.h x19, x17, 0x0b
    li x20, 0x000802a4
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x70ea0687
    pv.dotup.sci.h x19, x17, 0x15
    li x20, 0x0009cc45
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.dotup.b instruction. values loaded in and compared to are expected output values
#pv.dotup.b is of the form "pv.dotup.b rD, rs1, rs2"
test19:
    li x17, 0xc71e0ac8
    li x18, 0x04ae1745
    pv.dotup.b x19, x17, x18
    li x20, 0x00004e4e
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x155abaf5
    li x18, 0x13fe66b2
    pv.dotup.b x19, x17, x18
    li x20, 0x00014f51
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0x9d63534a
    li x18, 0xcde8e371
    pv.dotup.b x19, x17, x18
    li x20, 0x000141b4
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0x508b2b5d
    li x18, 0x51f8078f
    pv.dotup.b x19, x17, x18
    li x20, 0x0000d518
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0x0777091d
    li x18, 0xa1ac9cf4
    pv.dotup.b x19, x17, x18
    li x20, 0x0000757b
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0xadc46b3f
    li x18, 0x50cadfb3
    pv.dotup.b x19, x17, x18
    li x20, 0x000159fa
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.dotup.sc.b instruction. values loaded in and compared to are expected output values
#pv.or.sc.b is of the form "pv.dotup.sc.b rD, rs1, rs2"
test25:
    li x17, 0x723a555c
    li x18, 0xc58efe52
    pv.dotup.sc.b x19, x17, x18
    li x20, 0x00006fca
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0xad02556e
    li x18, 0xb8cce704
    pv.dotup.sc.b x19, x17, x18
    li x20, 0x00005c8
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0x25b8d3e3
    li x18, 0x6cf178db
    pv.dotup.sc.b x19, x17, x18
    li x20, 0x000233c1
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0xdab28669
    li x18, 0x3ec976e3
    pv.dotup.sc.b x19, x17, x18
    li x20, 0x00023311
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0xb8f9ec8f
    li x18, 0x50ca6bb5
    pv.dotup.sc.b x19, x17, x18
    li x20, 0x00023e1c
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0xbe578060
    li x18, 0x0b332fdd
    pv.dotup.sc.b x19, x17, x18
    li x20, 0x0001b081
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.dotup.sci.b instruction. values loaded in and compared to are expected output values
#pv.dotup.sci.b is of the form "pv.dotup.sci.b rD, rs1, Imm6"
test31:
    li x17, 0x375cf3e1
    pv.dotup.sci.b x19, x17, 0x0a
    li x20, 0x00001806
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0x741ff4fd
    pv.dotup.sci.b x19, x17, 0x02
    li x20, 0x00000508
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0x64379371
    pv.dotup.sci.b x19, x17, 0x1c
    li x20, 0x00002d64
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0x70095e27
    pv.dotup.sci.b x19, x17, 0x04
    li x20, 0x000003f8
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0xed23b04c
    pv.dotup.sci.b x19, x17, 0x08
    li x20, 0x00001060
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0xb73e73df
    pv.dotup.sci.b x19, x17, 0x0e
    li x20, 0x00001fe2
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.dotusp.h instruction. values loaded in and compared to are expected output values
#pv.dotusp.h is of the form "pv.dotusp.h rD, rs1, rs2"
test37:
    li x17, 0xc2b4bab2
    li x18, 0x28efdc3e
    pv.dotusp.h x19, x17, x18
    li x20, 0x050e1528
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0x361d7b9d
    li x18, 0xf44d555f
    pv.dotusp.h x19, x17, x18
    li x20, 0x26bfeafc
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0x8bcd51a1
    li x18, 0xe6af416e
    pv.dotusp.h x19, x17, x18
    li x20, 0x0709b351
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x10ca59e2
    li x18, 0x3d1144be
    pv.dotusp.h x19, x17, x18
    li x20, 0x1c23fd26
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0xbc490bca
    li x18, 0xb659cf99
    pv.dotusp.h x19, x17, x18
    li x20, 0xc799bd1b
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0xda832e89
    li x18, 0xa406e8ce
    pv.dotusp.h x19, x17, x18
    li x20, 0xad46a550
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.dotusp.sc.h instruction. values loaded in and compared to are expected output values
#pv.dotusp.sc.h is of the form "pv.dotusp.sc.h rD, rs1, rs2"
test43:
    li x17, 0x75d8c786
    li x18, 0x073d4040
    pv.dotusp.sc.h x19, x17, x18
    li x20, 0x4fa6d780
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0xc9de6255
    li x18, 0x4a01ff57
    pv.dotusp.sc.h x19, x17, x18
    li x20, 0xff39d255
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0xc5a6c38b
    li x18, 0xf78a072c
    pv.dotusp.sc.h x19, x17, x18
    li x20, 0x0b03eb6c
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0x007bee13
    li x18, 0x3a930631
    pv.dotusp.sc.h x19, x17, x18
    li x20, 0x05c4fd2e
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0xc18ca673
    li x18, 0x1d4c393f
    pv.dotusp.sc.h x19, x17, x18
    li x20, 0x50805ec1
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0xd1931c9c
    li x18, 0xc652343d
    pv.dotusp.sc.h x19, x17, x18
    li x20, 0x309a4d33
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.dotusp.sci.h instruction. values loaded in and compared to are expected output values
#pv.dotusp.sci.h is of the form "pv.dotusp.sci.h rD, rs1, Imm6"
test49:
    li x17, 0x9898f9da
    pv.dotusp.sci.h x19, x17, 0x0f
    li x20, 0x001794ae
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0x3906a14c
    pv.dotusp.sci.h x19, x17, 0x1f
    li x20, 0x001a6fee
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0x68b23822
    pv.dotusp.sci.h x19, x17, 0x05
    li x20, 0x00032424
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0x3f9fc689
    pv.dotusp.sci.h x19, x17, 0x14
    li x20, 0x00147b20
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x2cbd4d4d
    pv.dotusp.sci.h x19, x17, 0x0d
    li x20, 0x00063282
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0x767f1301
    pv.dotusp.sci.h x19, x17, 0x05
    li x20, 0x0002af80
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.dotusp.b instruction. values loaded in and compared to are expected output values
#pv.dotusp.b is of the form "pv.dotusp.b rD, rs1, rs2"
test55:
    li x17, 0x78b948eb
    li x18, 0xa10db278
    pv.dotusp.b x19, x17, x18
    li x20, 0x00003515
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0x8a0044d4
    li x18, 0x956ca42c
    pv.dotusp.b x19, x17, x18
    li x20, 0xffffd252
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0x1f438bc2
    li x18, 0xa2878bc4
    pv.dotusp.b x19, x17, x18
    li x20, 0xffff67f4
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0x441ff178
    li x18, 0x7b692489
    pv.dotusp.b x19, x17, x18
    li x20, 0x0000177f
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0xb2283b1a
    li x18, 0x70cf688f
    pv.dotusp.b x19, x17, x18
    li x20, 0x000052b6
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0x54cfaa4d
    li x18, 0xc917967e
    pv.dotusp.b x19, x17, x18
    li x20, 0xffffe00f
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.dotusp.sc.b instruction. values loaded in and compared to are expected output values
#pv.dotusp.sc.b is of the form "pv.dotusp.sc.b rD, rs1, rs2"
test61:
    li x17, 0x3288c6b0
    li x18, 0x0bc36aea
    pv.dotusp.sc.b x19, x17, x18
    li x20, 0xffffcfe0
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x2cd847f0
    li x18, 0x12d2fdbc
    pv.dotusp.sc.b x19, x17, x18
    li x20, 0xffff6854
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0xfca71bac
    li x18, 0x5fae1422
    pv.dotusp.sc.b x19, x17, x18
    li x20, 0x00005214
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0x8869ea62
    li x18, 0xafe8b45b
    pv.dotusp.sc.b x19, x17, x18
    li x20, 0x0000cbaf
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0x5c517c0b
    li x18, 0xe895d795
    pv.dotusp.sc.b x19, x17, x18
    li x20, 0xffff7f44
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0xeb055bef
    li x18, 0xe96cfb9b
    pv.dotusp.sc.b x19, x17, x18
    li x20, 0xffff1f1e
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.dotusp.sci.b instruction. values loaded in and compared to are expected output values
#pv.dotusp.sci.b is of the form "pv.dotusp.sci.b rD, rs1, Imm6"
test67:
    li x17, 0xa222991a
    pv.dotusp.sci.b x19, x17, 0x10
    li x20, 0x00001770
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0x7d071124
    pv.dotusp.sci.b x19, x17, 0x1d
    li x20, 0x000014f5
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0xcd97df91
    pv.dotusp.sci.b x19, x17, 0x0c
    li x20, 0x000021f0
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x3276e2da
    pv.dotusp.sci.b x19, x17, 0x0d
    li x20, 0x00001f14
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0xa4548d4c
    pv.dotusp.sci.b x19, x17, 0x07
    li x20, 0x00000cb7
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0xde5c08dd
    pv.dotusp.sci.b x19, x17, 0x06
    li x20, 0x00000cba
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.dotsp.h instruction. values loaded in and compared to are expected output values
#pv.dotsp.h is of the form "pv.dotsp.h rD, rs1, rs2"
test73:
    li x17, 0x32617430
    li x18, 0xf6237fd6
    pv.dotsp.h x19, x17, x18
    li x20, 0x38140963
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x17, 0x45670453
    li x18, 0x1c9fe38c
    pv.dotsp.h x19, x17, x18
    li x20, 0x0747555d
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x17, 0x1b9d05f3
    li x18, 0x466033ff
    pv.dotsp.h x19, x17, x18
    li x20, 0x08cc9eed
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x17, 0x62b680f5
    li x18, 0xd035b500
    pv.dotsp.h x19, x17, x18
    li x20, 0x12ca88ae
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x17, 0x3950ad4e
    li x18, 0x9f1fd488
    pv.dotsp.h x19, x17, x18
    li x20, 0xf85a4a20
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x17, 0xe6f68033
    li x18, 0x08f643ba
    pv.dotsp.h x19, x17, x18
    li x20, 0xdd501e72
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the pv.dotsp.sc.h instruction. values loaded in and compared to are expected output values
#pv.dotsp.sc.h is of the form "pv.dotsp.sc.h rD, rs1, rs2"
test79:
    li x17, 0x5f534237
    li x18, 0xe5f45f7a
    pv.dotsp.sc.h x19, x17, x18
    li x20, 0x3c3f31c4
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x17, 0xcc81894c
    li x18, 0x611b6e10
    pv.dotsp.sc.h x19, x17, x18
    li x20, 0xb6d372d0
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x17, 0xe4176d99
    li x18, 0x86264b2a
    pv.dotsp.sc.h x19, x17, x18
    li x20, 0x17fbf6e0
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x17, 0x1c248f32
    li x18, 0xdbf46889
    pv.dotsp.sc.h x19, x17, x18
    li x20, 0xdd6da106
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x17, 0x01dd1d61
    li x18, 0x801c5e19
    pv.dotsp.sc.h x19, x17, x18
    li x20, 0x0b7bd10e
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x17, 0xb203ff4e
    li x18, 0x4abc4ca3
    pv.dotsp.sc.h x19, x17, x18
    li x20, 0xe871f293
    beq x20, x19, test85
    c.addi x15, 0x1
#tests85-90 test the pv.dotsp.sci.h instruction. values loaded in and compared to are expected output values
#pv.dotsp.sci.h is of the form "pv.dotsp.sci.h rD, rs1, Imm6"
test85:
    li x17, 0xa0bf6c6c
    pv.dotsp.sci.h x19, x17, 0x0e
    li x20, 0x0000b85a
    beq x20, x19, test86
    c.addi x15, 0x1
test86:
    li x17, 0x11917e9e
    pv.dotsp.sci.h x19, x17, 0x1c
    li x20, 0x000fc524
    beq x20, x19, test87
    c.addi x15, 0x1
test87:
    li x17, 0x21d2135d
    pv.dotsp.sci.h x19, x17, 0x12
    li x20, 0x0003bd4e
    beq x20, x19, test88
    c.addi x15, 0x1
test88:
    li x17, 0xbf947e2a
    pv.dotsp.sci.h x19, x17, 0x1b
    li x20, 0x0006830a
    beq x20, x19, test89
    c.addi x15, 0x1
test89:
    li x17, 0x97068b1a
    pv.dotsp.sci.h x19, x17, 0x03
    li x20, 0xfffd6660
    beq x20, x19, test90
    c.addi x15, 0x1
test90:
    li x17, 0x44db3c7b
    pv.dotsp.sci.h x19, x17, 0x0d
    li x20, 0x0006915e
    beq x20, x19, test91
    c.addi x15, 0x1
#tests91-96 test the pv.dotsp.b instruction. values loaded in and compared to are expected output values
#pv.dotsp.b is of the form "pv.dotsp.b rD, rs1, rs2"
test91:
    li x17, 0x02fb75bc
    li x18, 0xd152ff76
    pv.dotsp.b x19, x17, x18
    li x20, 0xffffde3b
    beq x20, x19, test92
    c.addi x15, 0x1
test92:
    li x17, 0xb7336a6c
    li x18, 0xf24fbc1a
    pv.dotsp.b x19, x17, x18
    li x20, 0x0000028b
    beq x20, x19, test93
    c.addi x15, 0x1
test93:
    li x17, 0xaa3d6c3f
    li x18, 0x578240e4
    pv.dotsp.b x19, x17, x18
    li x20, 0xffffd8dc
    beq x20, x19, test94
    c.addi x15, 0x1
test94:
    li x17, 0xbebd393e
    li x18, 0x3720913c
    pv.dotsp.b x19, x17, x18
    li x20, 0xffffdf43
    beq x20, x19, test95
    c.addi x15, 0x1
test95:
    li x17, 0x8a6bc6b7
    li x18, 0x0e996134
    pv.dotsp.b x19, x17, x18
    li x20, 0xffffa9b1
    beq x20, x19, test96
    c.addi x15, 0x1
test96:
    li x17, 0x35eec174
    li x18, 0x5049b31c
    pv.dotsp.b x19, x17, x18
    li x20, 0x00002b11
    beq x20, x19, test97
    c.addi x15, 0x1
#tests97-102 test the pv.dotsp.sc.b instruction. values loaded in and compared to are expected output values
#pv.dotsp.sc.b is of the form "pv.dotsp.sc.b rD, rs1, rs2"
test97:
    li x17, 0x1db6da34
    li x18, 0x1b3a7736
    pv.dotsp.sc.b x19, x17, x18
    li x20, 0xfffff976
    beq x20, x19, test98
    c.addi x15, 0x1
test98:
    li x17, 0x02c6d241
    li x18, 0x0af8642e
    pv.dotsp.sc.b x19, x17, x18
    li x20, 0xfffff95a
    beq x20, x19, test99
    c.addi x15, 0x1
test99:
    li x17, 0x5da3634e
    li x18, 0x072c9c19
    pv.dotsp.sc.b x19, x17, x18
    li x20, 0x00001149
    beq x20, x19, test100
    c.addi x15, 0x1
test100:
    li x17, 0x3c0d1c41
    li x18, 0x5cf64a54
    pv.dotsp.sc.b x19, x17, x18
    li x20, 0x00003678
    beq x20, x19, test101
    c.addi x15, 0x1
test101:
    li x17, 0x9b8c5402
    li x18, 0x1b5c9218
    pv.dotsp.sc.b x19, x17, x18
    li x20, 0xfffff3b8
    beq x20, x19, test102
    c.addi x15, 0x1
test102:
    li x17, 0x60aeb8a3
    li x18, 0x58050242
    pv.dotsp.sc.b x19, x17, x18
    li x20, 0xffffd912
    beq x20, x19, test103
    c.addi x15, 0x1
#tests103-108 test the pv.dotsp.sci.b instruction. values loaded in and compared to are expected output values
#pv.dotsp.sci.b is of the form "pv.dotsp.sci.b rD, rs1, Imm6"
test103:
    li x17, 0x46e895d9
    pv.dotsp.sci.b x19, x17, 0x05
    li x20, 0xfffffe0c
    beq x20, x19, test104
    c.addi x15, 0x1
test104:
    li x17, 0x28846a49
    pv.dotsp.sci.b x19, x17, 0x01
    li x20, 0x0000005f
    beq x20, x19, test105
    c.addi x15, 0x1
test105:
    li x17, 0x8f4ffd41
    pv.dotsp.sci.b x19, x17, 0x12
    li x20, 0x000001f8
    beq x20, x19, test106
    c.addi x15, 0x1
test106:
    li x17, 0x547d9f3a
    pv.dotsp.sci.b x19, x17, 0x18
    li x20, 0x00000ff0
    beq x20, x19, test107
    c.addi x15, 0x1
test107:
    li x17, 0xa83cc2f9
    pv.dotsp.sci.b x19, x17, 0x04
    li x20, 0xfffffe7c
    beq x20, x19, test108
    c.addi x15, 0x1
test108:
    li x17, 0xc97c4baf
    pv.dotsp.sci.b x19, x17, 0x10
    li x20, 0x000003f0
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
