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
#tests1-6 test the pv.avg.h instruction. values loaded in and compared to are expected output values
#pv.avg.h is of the form "pv.avg.h rD, rs1, rs2". rD[31:16] = (rs1[31:16]+rs2[31:16])>>>1, (rD[15:0] = rs1[15:0]+rs2[15:0])>>>1
test1:
    li x17, 0x39c819bc
    li x18, 0x722ce8a9
    pv.avg.h x19, x17, x18
    li x20, 0xd5fa0132
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x123d66be
    li x18, 0x1b745655
    pv.avg.h x19, x17, x18
    li x20, 0x16d8de89
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0xacd77a02
    li x18, 0x5ae12939
    pv.avg.h x19, x17, x18
    li x20, 0x03dcd19d
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0xf684d787
    li x18, 0x620f6498
    pv.avg.h x19, x17, x18
    li x20, 0x2c491e0f
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0xf548798a
    li x18, 0x9f245010
    pv.avg.h x19, x17, x18
    li x20, 0xca36e4cd
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x9748e90c
    li x18, 0x7a834018
    pv.avg.h x19, x17, x18
    li x20, 0x08e51492
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.avg.sc.h instruction. values loaded in and compared to are expected output values
#pv.avg.sc.h is of the form "pv.avg.sc.h rD, rs1, rs2". rD[31:16] = (rs1[31:16]+rs2[15:0])>>>1, (rD[15:0] = rs1[15:0]+rs2[15:0])>>>1
test7:
    li x17, 0x39c819bc
    li x18, 0x722ce8a9
    pv.avg.sc.h x19, x17, x18
    li x20, 0x11380132
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x123d66be
    li x18, 0x1b745655
    pv.avg.sc.h x19, x17, x18
    li x20, 0x3449de89
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0xacd77a02
    li x18, 0x5ae12939
    pv.avg.sc.h x19, x17, x18
    li x20, 0xeb08d19d
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0xf684d787
    li x18, 0x620f6498
    pv.avg.sc.h x19, x17, x18
    li x20, 0x2d8e1e0f
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0xf548798a
    li x18, 0x9f245010
    pv.avg.sc.h x19, x17, x18
    li x20, 0x22ace4cd
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x9748e90c
    li x18, 0x7a834018
    pv.avg.sc.h x19, x17, x18
    li x20, 0xebb01492
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.avg.sci.h instruction. values loaded in and compared to are expected output values
#pv.avg.sci.h is of the form "pv.avg.sci.h rD, rs1, Imm6". rD[31:16] = (rs1[31:16]+Imm6)>>>1, (rD[15:0] = rs1[15:0]+Imm6)>>>1
test13:
    li x17, 0x3f93d54c
    pv.avg.sci.h x19, x17, 0x18
    li x20, 0x1fd5eab2
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0xa82ba368
    pv.avg.sci.h x19, x17, 0x09
    li x20, 0xd41ad1b8
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0xa3391d9d
    pv.avg.sci.h x19, x17, 0x14
    li x20, 0xd1a60ed8
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0x2ceae9ad
    pv.avg.sci.h x19, x17, 0x01
    li x20, 0x1675f4d7
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x8efc1970
    pv.avg.sci.h x19, x17, 0x1f
    li x20, 0xc78d0cc7
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x8e2f9a75
    pv.avg.sci.h x19, x17, 0x05
    li x20, 0xc71acd3d
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.avg.b instruction. values loaded in and compared to are expected output values
#pv.avg.b is of the form "pv.avg.b rD, rs1, rs2". rD[31:16] = (rs1[31:24]+rs2[31:24])>>>1,
#rD[23:16] = (rs1[23:16]+rs2[23:16])>>>1, (rD[15:8] = rs1[15:8]+rs2[15:8])>>>1. (rD[7:0] = rs1[7:0]+rs2[7:0])>>>1
test19:
    li x17, 0x39c819bc
    li x18, 0x722ce8a9
    pv.avg.b x19, x17, x18
    li x20, 0xd5fa0032
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x123d66be
    li x18, 0x1b745655
    pv.avg.b x19, x17, x18
    li x20, 0x16d8de09
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0xacd77a02
    li x18, 0x5ae12939
    pv.avg.b x19, x17, x18
    li x20, 0x03dcd11d
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0xf684d787
    li x18, 0x620f6498
    pv.avg.b x19, x17, x18
    li x20, 0x2cc91d0f
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0xf548798a
    li x18, 0x9f245010
    pv.avg.b x19, x17, x18
    li x20, 0xca36e4cd
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0x9748e90c
    li x18, 0x7a834018
    pv.avg.b x19, x17, x18
    li x20, 0x08e51412
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.avg.sc.b instruction. values loaded in and compared to are expected output values
#pv.avg.sc.b is of the form "pv.avg.sc.b rD, rs1, rs2". rD[31:16] = (rs1[31:24]+rs2[7:0])>>>1,
#rD[23:16] = (rs1[23:16]+rs2[7:106])>>>1, (rD[15:8] = rs1[15:8]+rs2[7:0])>>>1. (rD[7:0] = rs1[7:0]+rs2[7:0])>>>1
test25:
    li x17, 0x39c819bc
    li x18, 0x722ce8a9
    pv.avg.sc.b x19, x17, x18
    li x20, 0xf138e132
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x123d66be
    li x18, 0x1b745655
    pv.avg.sc.b x19, x17, x18
    li x20, 0x33c9dd09
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0xacd77a02
    li x18, 0x5ae12939
    pv.avg.sc.b x19, x17, x18
    li x20, 0xf208d91d
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0xf684d787
    li x18, 0x620f6498
    pv.avg.sc.b x19, x17, x18
    li x20, 0xc70e370f
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0xf548798a
    li x18, 0x9f245010
    pv.avg.sc.b x19, x17, x18
    li x20, 0x022cc4cd
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0x9748e90c
    li x18, 0x7a834018
    pv.avg.sc.b x19, x17, x18
    li x20, 0xd7300012
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.avg.sci.b instruction. values loaded in and compared to are expected output values
#pv.avg.sci.b is of the form "pv.avg.sci.b rD, rs1, Imm6". rD[31:16] = (rs1[31:24]+Imm6)>>>1,
#rD[23:16] = (rs1[23:16]+Imm6)>>>1, (rD[15:8] = rs1[15:8]+Imm6)>>>1. (rD[7:0] = rs1[7:0]+Imm6)>>>1
test31:
    li x17, 0x3f93d54c
    pv.avg.sci.b x19, x17, 0x18
    li x20, 0x2bd5f632
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0xa82ba368
    pv.avg.sci.b x19, x17, 0x09
    li x20, 0xd81ad638
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0xa3391d9d
    pv.avg.sci.b x19, x17, 0x14
    li x20, 0xdb2618d8
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0x2ceae9ad
    pv.avg.sci.b x19, x17, 0x01
    li x20, 0x16f5f5d7
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x8efc1970
    pv.avg.sci.b x19, x17, 0x1f
    li x20, 0xd60d1cc7
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0x8e2f9a75
    pv.avg.sci.b x19, x17, 0x05
    li x20, 0xc91acf3d
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.avgu.h instruction. values loaded in and compared to are expected output values
#pv.avgu.h is of the form "pv.avgu.h rD, rs1, rs2". rD[31:16] = (rs1[31:16]+rs2[31:16])>>1, (rD[15:0] = rs1[15:0]+rs2[15:0])>>1
test37:
    li x17, 0x39c819bc
    li x18, 0x722ce8a9
    pv.avgu.h x19, x17, x18
    li x20, 0x55fa0132
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0x123d66be
    li x18, 0x1b745655
    pv.avgu.h x19, x17, x18
    li x20, 0x16d85e89
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0xacd77a02
    li x18, 0x5ae12939
    pv.avgu.h x19, x17, x18
    li x20, 0x03dc519d
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0xf684d787
    li x18, 0x620f6498
    pv.avgu.h x19, x17, x18
    li x20, 0x2c491e0f
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0xf548798a
    li x18, 0x9f245010
    pv.avgu.h x19, x17, x18
    li x20, 0x4a3664cd
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0x9748e90c
    li x18, 0x7a834018
    pv.avgu.h x19, x17, x18
    li x20, 0x08e51492
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.avgu.sc.h instruction. values loaded in and compared to are expected output values
#pv.avgu.sc.h is of the form "pv.avgu.sc.h rD, rs1, rs2". rD[31:16] = (rs1[31:16]+rs2[15:0])>>1, (rD[15:0] = rs1[15:0]+rs2[15:0])>>1
test43:
    li x17, 0x39c819bc
    li x18, 0x722ce8a9
    pv.avgu.sc.h x19, x17, x18
    li x20, 0x11380132
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0x123d66be
    li x18, 0x1b745655
    pv.avgu.sc.h x19, x17, x18
    li x20, 0x34495e89
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0xacd77a02
    li x18, 0x5ae12939
    pv.avgu.sc.h x19, x17, x18
    li x20, 0x6b08519d
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0xf684d787
    li x18, 0x620f6498
    pv.avgu.sc.h x19, x17, x18
    li x20, 0x2d8e1e0f
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0xf548798a
    li x18, 0x9f245010
    pv.avgu.sc.h x19, x17, x18
    li x20, 0x22ac64cd
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0x9748e90c
    li x18, 0x7a834018
    pv.avgu.sc.h x19, x17, x18
    li x20, 0x6bb01492
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.avgu.sci.h instruction. values loaded in and compared to are expected output values
#pv.avgu.sci.h is of the form "pv.avgu.sci.h rD, rs1, Imm6". rD[31:16] = (rs1[31:16]+Imm6)>>1, (rD[15:0] = rs1[15:0]+Imm6)>>1
test49:
    li x17, 0x3f93d54c
    pv.avgu.sci.h x19, x17, 0x18
    li x20, 0x1fd56ab2
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0xa82ba368
    pv.avgu.sci.h x19, x17, 0x09
    li x20, 0x541a51b8
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0xa3391d9d
    pv.avgu.sci.h x19, x17, 0x14
    li x20, 0x51a60ed8
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0x2ceae9ad
    pv.avgu.sci.h x19, x17, 0x01
    li x20, 0x167574d7
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x8efc1970
    pv.avgu.sci.h x19, x17, 0x1f
    li x20, 0x478d0cc7
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0x8e2f9a75
    pv.avgu.sci.h x19, x17, 0x05
    li x20, 0x471a4d3d
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.avgu.b instruction. values loaded in and compared to are expected output values
#pv.avgu.b is of the form "pv.avgu.b rD, rs1, rs2". rD[31:16] = (rs1[31:24]+rs2[31:24])>>1,
#rD[23:16] = (rs1[23:16]+rs2[23:16])>>1, (rD[15:8] = rs1[15:8]+rs2[15:8])>>1. (rD[7:0] = rs1[7:0]+rs2[7:0])>>1
test55:
    li x17, 0x39c819bc
    li x18, 0x722ce8a9
    pv.avgu.b x19, x17, x18
    li x20, 0x557a0032
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0x123d66be
    li x18, 0x1b745655
    pv.avgu.b x19, x17, x18
    li x20, 0x16585e09
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0xacd77a02
    li x18, 0x5ae12939
    pv.avgu.b x19, x17, x18
    li x20, 0x035c511d
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0xf684d787
    li x18, 0x620f6498
    pv.avgu.b x19, x17, x18
    li x20, 0x2c491d0f
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0xf548798a
    li x18, 0x9f245010
    pv.avgu.b x19, x17, x18
    li x20, 0x4a36644d
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0x9748e90c
    li x18, 0x7a834018
    pv.avgu.b x19, x17, x18
    li x20, 0x08651412
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.avgu.sc.b instruction. values loaded in and compared to are expected output values
#pv.avgu.sc.b is of the form "pv.avgu.sc.b rD, rs1, rs2". rD[31:16] = (rs1[31:24]+rs2[7:0])>>1,
#rD[23:16] = (rs1[23:16]+rs2[7:106])>>1, (rD[15:8] = rs1[15:8]+rs2[7:0])>>1. (rD[7:0] = rs1[7:0]+rs2[7:0])>>1
test61:
    li x17, 0x39c819bc
    li x18, 0x722ce8a9
    pv.avgu.sc.b x19, x17, x18
    li x20, 0x71386132
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x123d66be
    li x18, 0x1b745655
    pv.avgu.sc.b x19, x17, x18
    li x20, 0x33495d09
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0xacd77a02
    li x18, 0x5ae12939
    pv.avgu.sc.b x19, x17, x18
    li x20, 0x7208591d
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0xf684d787
    li x18, 0x620f6498
    pv.avgu.sc.b x19, x17, x18
    li x20, 0x470e370f
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0xf548798a
    li x18, 0x9f245010
    pv.avgu.sc.b x19, x17, x18
    li x20, 0x022c444d
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0x9748e90c
    li x18, 0x7a834018
    pv.avgu.sc.b x19, x17, x18
    li x20, 0x57300012
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.avgu.sci.b instruction. values loaded in and compared to are expected output values
#pv.avgu.sci.b is of the form "pv.avgu.sci.b rD, rs1, Imm6". rD[31:16] = (rs1[31:24]+Imm6)>>1,
#rD[23:16] = (rs1[23:16]+Imm6)>>1, (rD[15:8] = rs1[15:8]+Imm6)>>1. (rD[7:0] = rs1[7:0]+Imm6)>>1
test67:
    li x17, 0x3f93d54c
    pv.avgu.sci.b x19, x17, 0x18
    li x20, 0x2b557632
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0xa82ba368
    pv.avgu.sci.b x19, x17, 0x09
    li x20, 0x581a5638
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0xa3391d9d
    pv.avgu.sci.b x19, x17, 0x14
    li x20, 0x5b261858
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x2ceae9ad
    pv.avgu.sci.b x19, x17, 0x01
    li x20, 0x16757557
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0x8efc1970
    pv.avgu.sci.b x19, x17, 0x1f
    li x20, 0x560d1c47
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0x8e2f9a75
    pv.avgu.sci.b x19, x17, 0x05
    li x20, 0x491a4f3d
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.abs.h instruction. values loaded in and compared to are expected output values
#pv.abs.h is of the form "pv.abs.h rD, rs1, rs2".
test73:
    li x17, 0xccb59b65
    pv.abs.h x19, x17
    li x20, 0x334b649b
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x17, 0xb6a36d61
    pv.abs.h x19, x17
    li x20, 0x495d6d61
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x17, 0xd540fa50
    pv.abs.h x19, x17
    li x20, 0x2ac005b0
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x17, 0x97f2acad
    pv.abs.h x19, x17
    li x20, 0x680e5353
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x17, 0x84def8bd
    pv.abs.h x19, x17
    li x20, 0x7b220743
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x17, 0x602a4434
    pv.abs.h x19, x17
    li x20, 0x602a4434
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the pv.abs.b instruction. values loaded in and compared to are expected output values
#pv.abs.b is of the form "pv.abs.b rD, rs1, rs2".
test79:
    li x17, 0x9168aff7
    pv.abs.b x19, x17
    li x20, 0x6f685109
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x17, 0x95422b18
    pv.abs.b x19, x17
    li x20, 0x6b422b18
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x17, 0x786d4744
    pv.abs.b x19, x17
    li x20, 0x786d4744
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x17, 0x4c122684
    pv.abs.b x19, x17
    li x20, 0x4c12267c
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x17, 0x52f42286
    pv.abs.b x19, x17
    li x20, 0x520c227a
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x17, 0x4682c47d
    pv.abs.b x19, x17
    li x20, 0x467e3c7d
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
