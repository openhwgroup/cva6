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
#tests1-6 test the pv.add.h instruction. values loaded in and compared to are expected output values
#pv.add.h is of the form "pv.add.h rD, rs1, rs2". rD[31:16] = rs1[31:16]+rs2[31:16], rD[15:0] = rs1[15:0]+rs2[15:0]
test1:
    li x17, 0xa42e5f23
    li x18, 0x03f5b3ae
    pv.add.h x19, x17, x18
    li x20, 0xa82312d1
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x923812e3
    li x18, 0xee2f2fa8
    pv.add.h x19, x17, x18
    li x20, 0x8067428b
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0x7bd6778c
    li x18, 0x4ae75eb2
    pv.add.h x19, x17, x18
    li x20, 0xc6bdd63e
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x53f30da3
    li x18, 0xd550292f
    pv.add.h x19, x17, x18
    li x20, 0x294336d2
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0x7b35a243
    li x18, 0x21b9f9b3
    pv.add.h x19, x17, x18
    li x20, 0x9cee9bf6
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x4deed767
    li x18, 0xe8baa301
    pv.add.h x19, x17, x18
    li x20, 0x36a87a68
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.add.sc.h instruction. values loaded in and compared to are expected output values
#pv.add.sc.h is of the form "pv.add.sc.h rD, rs1, rs2". rD[31:16] = rs1[31:16]+rs2[15:0], rD[15:0] = rs1[15:0]+rs2[15:0]
test7:
    li x17, 0x040193eb
    li x18, 0x655fe439
    pv.add.sc.h x19, x17, x18
    li x20, 0xe83a7824
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x24db2f5e
    li x18, 0x8734e438
    pv.add.sc.h x19, x17, x18
    li x20, 0x09131396
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x77ccab0d
    li x18, 0x05d2692b
    pv.add.sc.h x19, x17, x18
    li x20, 0xe0f71438
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0xa6cb5330
    li x18, 0x5e2078a1
    pv.add.sc.h x19, x17, x18
    li x20, 0x1f6ccbd1
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0xdc856605
    li x18, 0x0de722a9
    pv.add.sc.h x19, x17, x18
    li x20, 0xff2e88ae
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x305d6141
    li x18, 0x4ae3e9cc
    pv.add.sc.h x19, x17, x18
    li x20, 0x1a294b0d
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.add.sci.h instruction. values loaded in and compared to are expected output values
#pv.add.sci.h is of the form "pv.add.sci.h rD, rs1, Imm6". rD[31:16] = rs1[31:16]+Sext(Imm6), rD[15:0] = rs1[15:0]+Sext(Imm6)
test13:
    li x17, 0x993f35ed
    pv.add.sci.h x19, x17, 0x0e
    li x20, 0x994d35fb
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0x03ee3d4b
    pv.add.sci.h x19, x17, 0x04
    li x20, 0x03f23d4f
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0xed29a590
    pv.add.sci.h x19, x17, 0x1c
    li x20, 0xed45a5ac
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0xa74684d2
    pv.add.sci.h x19, x17, 0x08
    li x20, 0xa74e84da
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x6714ae3f
    pv.add.sci.h x19, x17, 0x14
    li x20, 0x6728ae53
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x81899f05
    pv.add.sci.h x19, x17, 0x1c
    li x20, 0x81a59f21
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.add.b instruction. values loaded in and compared to are expected output values
#pv.add.b is of the form "pv.add.b rD, rs1, rs2". rD[31:24] = rs1[31:24]+rs2[31:24]
#rD[23:16] = rs1[23:16]+rs2[23:16], rD[15:8] = rs1[15:8]+rs2[15:8], rD[7:0] = rs1[7:0]+rs2[7:0]
test19:
    li x17, 0x97f73b3e
    li x18, 0x4cb3e882
    pv.add.b x19, x17, x18
    li x20, 0xe3aa23c0
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x819ffec2
    li x18, 0xeef9e3e9
    pv.add.b x19, x17, x18
    li x20, 0x6f98e1ab
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0xd3769c0c
    li x18, 0xf2b49c73
    pv.add.b x19, x17, x18
    li x20, 0xc52a387f
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0xc6e280fc
    li x18, 0x4645719c
    pv.add.b x19, x17, x18
    li x20, 0x0c27f198
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0x4a13436e
    li x18, 0x2e6560e9
    pv.add.b x19, x17, x18
    li x20, 0x7878a357
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0x5d1d4055
    li x18, 0x027aaaf3
    pv.add.b x19, x17, x18
    li x20, 0x5f97ea48
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.add.sc.b instruction. values loaded in and compared to are expected output values
#pv.add.sc.b is of the form "pv.add.sc.b rD, rs1, rs2". rD[31:24] = rs1[31:24]+rs2[7:0]
#rD[23:16] = rs1[23:16]+rs2[7:0], rD[15:8] = rs1[15:8]+rs2[7:0], rD[7:0] = rs1[7:0]+rs2[7:0]
test25:
    li x17, 0xfc057499
    li x18, 0xbac6cac2
    pv.add.sc.b x19, x17, x18
    li x20, 0xbec7365b
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x8b91e0d7
    li x18, 0xb5b54608
    pv.add.sc.b x19, x17, x18
    li x20, 0x9399e8df
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0x2dfdd9d1
    li x18, 0xa26efc40
    pv.add.sc.b x19, x17, x18
    li x20, 0x6d3d1911
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0x19e2b1d4
    li x18, 0x95260c42
    pv.add.sc.b x19, x17, x18
    li x20, 0x5b24f316
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0x919df356
    li x18, 0xf016c712
    pv.add.sc.b x19, x17, x18
    li x20, 0xa3af0568
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0x7708106a
    li x18, 0xc6f84497
    pv.add.sc.b x19, x17, x18
    li x20, 0x0e9fa701
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.add.sci.b instruction. values loaded in and compared to are expected output values
#pv.add.sci.b is of the form "pv.add.sci.b rD, rs1, Imm6". rD[31:24] = rs1[31:24]+Sext(Imm6),
# rD[23:16] = rs1[23:16]+Sext(Imm6), rD[15:8] = rs1[15:8]+Sext(Imm6), rD[7:0] = rs1[7:0]+Sext(Imm6)
test31:
    li x17, 0x3d5951bd
    pv.add.sci.b x19, x17, 0x1f
    li x20, 0x5c7870dc
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0xb047c2fe
    pv.add.sci.b x19, x17, 0x08
    li x20, 0xb84fca06
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0x7dbe6ba0
    pv.add.sci.b x19, x17, 0x16
    li x20, 0x93d481b6
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0xed9e0824
    pv.add.sci.b x19, x17, 0x0c
    li x20, 0xf9aa1430
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x25c7f6f6
    pv.add.sci.b x19, x17, 0x0b
    li x20, 0x30d20101
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0x1f63428e
    pv.add.sci.b x19, x17, 0x13
    li x20, 0x327655a1
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.add.div2 instruction. values loaded in and compared to are expected output values
#pv.add.div2 is of the form "pv.add.div2 rD, rs1, rs2". rD[31:16] = (rs1[31:16] + rs2[31:16])>>1
#rD [15:0] = (rs1[15:0] + rs2[15:0])>>1
test37:
    li x17, 0xf14b3729
    li x18, 0xa6dffa04
    .word 0x7528a9d7    #pv.add.div2 x19, x17, x18
    li x20, 0x4c151896
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0x615a3814
    li x18, 0x0b218a1d
    .word 0x7528a9d7    #pv.add.div2 x19, x17, x18
    li x20, 0x363d6118
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0x899b9daa
    li x18, 0xc799bf72
    .word 0x7528a9d7    #pv.add.div2 x19, x17, x18
    li x20, 0x289a2e8e
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x784a98e3
    li x18, 0xa5385e64
    .word 0x7528a9d7    #pv.add.div2 x19, x17, x18
    li x20, 0x0ec17ba3
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0xa80f53e9
    li x18, 0xe3e07c1e
    .word 0x7528a9d7    #pv.add.div2 x19, x17, x18
    li x20, 0x45f76803
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0x721f17b7
    li x18, 0xca3256f2
    .word 0x7528a9d7    #pv.add.div2 x19, x17, x18
    li x20, 0x1e283754
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.add.div4 instruction. values loaded in and compared to are expected output values
#pv.add.div4 is of the form "pv.add.div4 rD, rs1, rs2". rD[31:16] = (rs1[31:16] + rs2[31:16])>>2
#rD [15:0] = (rs1[15:0] + rs2[15:0])>>2
test43:
    li x17, 0xf996c75d
    li x18, 0x6fcc0d8b
    .word 0x7528c9d7    #pv.add.div4 x19, x17, x18
    li x20, 0x1a58353a
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0x1ace57a3
    li x18, 0x5a105f37
    .word 0x7528c9d7    #pv.add.div4 x19, x17, x18
    li x20, 0x1d372db6
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0xa4a93062
    li x18, 0x2f1a9732
    .word 0x7528c9d7    #pv.add.div4 x19, x17, x18
    li x20, 0x34f031e5
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0x842aeebb
    li x18, 0xf8ec8340
    .word 0x7528c9d7    #pv.add.div4 x19, x17, x18
    li x20, 0x1f451c7e
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0xae2beb6d
    li x18, 0x2881cd1c
    .word 0x7528c9d7    #pv.add.div4 x19, x17, x18
    li x20, 0x35ab2e22
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0xe0de49ca
    li x18, 0xeda89810
    .word 0x7528c9d7    #pv.add.div4 x19, x17, x18
    li x20, 0x33a13876
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.add.div8 instruction. values loaded in and compared to are expected output values
#pv.add.div8 is of the form "pv.add.div8 rD, rs1, rs2". rD[31:16] = (rs1[31:16] + rs2[31:16])>>3
#rD [15:0] = (rs1[15:0] + rs2[15:0])>>3
test49:
    li x17, 0x00f0091b
    li x18, 0x04868a8f
    .word 0x7528e9d7    #pv.add.div8 x19, x17, x18
    li x20, 0x00ae1275
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0x349f1c44
    li x18, 0xde7a69e0
    .word 0x7528e9d7    #pv.add.div8 x19, x17, x18
    li x20, 0x026310c4
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0x453011b7
    li x18, 0x855ce1b1
    .word 0x7528e9d7    #pv.add.div8 x19, x17, x18
    li x20, 0x19511e6d
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0x4e544def
    li x18, 0xf63d2d7f
    .word 0x7528e9d7    #pv.add.div8 x19, x17, x18
    li x20, 0x08920f6d
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x751ed585
    li x18, 0xed1fed20
    .word 0x7528e9d7    #pv.add.div8 x19, x17, x18
    li x20, 0x0c471854
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0x1b1b67d7
    li x18, 0xf758297f
    .word 0x7528e9d7    #pv.add.div8 x19, x17, x18
    li x20, 0x024e122a
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.sub.h instruction. values loaded in and compared to are expected output values
#pv.sub.h is of the form "pv.sub.h rD, rs1, rs2". rD[31:16] = rs1[31:16]-rs2[31:16], rD[15:0] = rs1[15:0]-rs2[15:0]
test55:
    li x17, 0xa5fe61e9
    li x18, 0x6d2eada6
    pv.sub.h x19, x17, x18
    li x20, 0x38d0b443
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0x20518159
    li x18, 0x47c10ed4
    pv.sub.h x19, x17, x18
    li x20, 0xd8907285
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0x5e2f82f7
    li x18, 0xf7cbed64
    pv.sub.h x19, x17, x18
    li x20, 0x66649593
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0xee25be40
    li x18, 0xccbbfaf0
    pv.sub.h x19, x17, x18
    li x20, 0x216ac350
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0x2151d226
    li x18, 0x8011f883
    pv.sub.h x19, x17, x18
    li x20, 0xa140d9a3
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0x80236713
    li x18, 0xc1a1aa5e
    pv.sub.h x19, x17, x18
    li x20, 0xbe82bcb5
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.sub.sc.h instruction. values loaded in and compared to are expected output values
#pv.sub.sc.h is of the form "pv.sub.sc.h rD, rs1, rs2". rD[31:16] = rs1[31:16]+rs2[15:0], rD[15:0] = rs1[15:0]+rs2[15:0]
test61:
    li x17, 0xfe8eb60b
    li x18, 0xb11d10d1
    pv.sub.sc.h x19, x17, x18
    li x20, 0xedbda53a
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x9187649a
    li x18, 0x7c609474
    pv.sub.sc.h x19, x17, x18
    li x20, 0xfd13d026
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0x649a11cc
    li x18, 0x790f41cf
    pv.sub.sc.h x19, x17, x18
    li x20, 0x22cbcffd
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0x67047842
    li x18, 0xd54a4072
    pv.sub.sc.h x19, x17, x18
    li x20, 0x269237d0
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0x455e1a95
    li x18, 0x2b3e5493
    pv.sub.sc.h x19, x17, x18
    li x20, 0xf0cbc602
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0x4684179b
    li x18, 0xe41321d8
    pv.sub.sc.h x19, x17, x18
    li x20, 0x24acf5c3
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.sub.sci.h instruction. values loaded in and compared to are expected output values
#pv.sub.sci.h is of the form "pv.sub.sci.h rD, rs1, Imm6". rD[31:16] = rs1[31:16]+Sext(Imm6), rD[15:0] = rs1[15:0]+Sext(Imm6)
test67:
    li x17, 0x9a8a18dc
    pv.sub.sci.h x19, x17, 0x1f
    li x20, 0x9a6b18bd
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0x34088d99
    pv.sub.sci.h x19, x17, 0x01
    li x20, 0x34078d98
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0x6864ab38
    pv.sub.sci.h x19, x17, 0x04
    li x20, 0x6860ab34
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x97148fd8
    pv.sub.sci.h x19, x17, 0x0c
    li x20, 0x97088fcc
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0xe19b7596
    pv.sub.sci.h x19, x17, 0x07
    li x20, 0xe194758f
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0x93064ffd
    pv.sub.sci.h x19, x17, 0x1d
    li x20, 0x92e94fe0
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.sub.b instruction. values loaded in and compared to are expected output values
#pv.sub.b is of the form "pv.sub.b rD, rs1, rs2". rD[31:24] = rs1[31:24]+rs2[31:24]
#rD[23:16] = rs1[23:16]+rs2[23:16], rD[15:8] = rs1[15:8]+rs2[15:8], rD[7:0] = rs1[7:0]+rs2[7:0]
test73:
    li x17, 0x18f69b81
    li x18, 0xb3d5eeba
    pv.sub.b x19, x17, x18
    li x20, 0x6521adc7
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x17, 0x6b6281ef
    li x18, 0xc61239c3
    pv.sub.b x19, x17, x18
    li x20, 0xa550482c
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x17, 0xef63bce7
    li x18, 0xbe238abf
    pv.sub.b x19, x17, x18
    li x20, 0x31403228
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x17, 0x2bf0c91d
    li x18, 0x89db9b85
    pv.sub.b x19, x17, x18
    li x20, 0xa2152e98
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x17, 0xe7c8f49f
    li x18, 0x79b65283
    pv.sub.b x19, x17, x18
    li x20, 0x6e12a21c
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x17, 0x7dc527aa
    li x18, 0xb6039765
    pv.sub.b x19, x17, x18
    li x20, 0xc7c29045
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the pv.sub.sc.b instruction. values loaded in and compared to are expected output values
#pv.sub.sc.b is of the form "pv.sub.sc.b rD, rs1, rs2". rD[31:24] = rs1[31:24]-rs2[7:0]
#rD[23:16] = rs1[23:16]-rs2[7:0], rD[15:8] = rs1[15:8]-rs2[7:0], rD[7:0] = rs1[7:0]-rs2[7:0]
test79:
    li x17, 0xedf1ec44
    li x18, 0xf8ec82e9
    pv.sub.sc.b x19, x17, x18
    li x20, 0x0408035b
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x17, 0x842c8cb3
    li x18, 0x124ce9f4
    pv.sub.sc.b x19, x17, x18
    li x20, 0x903898bf
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x17, 0xea3a9a7f
    li x18, 0x141e3ab2
    pv.sub.sc.b x19, x17, x18
    li x20, 0x3888e8cd
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x17, 0x189e6733
    li x18, 0x2fdab0cd
    pv.sub.sc.b x19, x17, x18
    li x20, 0x4bd19a66
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x17, 0x97448d7f
    li x18, 0x704caa6c
    pv.sub.sc.b x19, x17, x18
    li x20, 0x2bd82113
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x17, 0x445a3f73
    li x18, 0x1da0d110
    pv.sub.sc.b x19, x17, x18
    li x20, 0x344a2f63
    beq x20, x19, test85
    c.addi x15, 0x1
#tests85-90 test the pv.sub.sci.b instruction. values loaded in and compared to are expected output values
#pv.sub.sci.b is of the form "pv.sub.sci.b rD, rs1, Imm6". rD[31:24] = rs1[31:24]-Sext(Imm6),
# rD[23:16] = rs1[23:16]-Sext(Imm6), rD[15:8] = rs1[15:8]-Sext(Imm6), rD[7:0] = rs1[7:0]-Sext(Imm6)
test85:
    li x17, 0x436049c4
    pv.sub.sci.b x19, x17, 0x10
    li x20, 0x335039b4
    beq x20, x19, test86
    c.addi x15, 0x1
test86:
    li x17, 0xa78cafc4
    pv.sub.sci.b x19, x17, 0x02
    li x20, 0xa58aadc2
    beq x20, x19, test87
    c.addi x15, 0x1
test87:
    li x17, 0x5afd71c3
    pv.sub.sci.b x19, x17, 0x13
    li x20, 0x47ea5eb0
    beq x20, x19, test88
    c.addi x15, 0x1
test88:
    li x17, 0xa7e5eff7
    pv.sub.sci.b x19, x17, 0x0a
    li x20, 0x9ddbe5ed
    beq x20, x19, test89
    c.addi x15, 0x1
test89:
    li x17, 0x79254ad8
    pv.sub.sci.b x19, x17, 0x08
    li x20, 0x711d42d0
    beq x20, x19, test90
    c.addi x15, 0x1
test90:
    li x17, 0x7a009533
    pv.sub.sci.b x19, x17, 0x11
    li x20, 0x69ef8422
    beq x20, x19, test91
    c.addi x15, 0x1
#tests90-96 test the pv.sub.div2 instruction. values loaded in and compared to are expected output values
#pv.sub.div2 is of the form "pv.sub.div2 rD, rs1, rs2". rD[31:16] = (rs1[31:16] - rs2[31:16])>>1
#rD [15:0] = (rs1[15:0] - rs2[15:0])>>1
test91:
    li x17, 0xdb0ab431
    li x18, 0x8c72f00e
    .word 0x6528a9d7    #pv.sub.div2 x19, x17, x18
    li x20, 0x274c6211
    beq x20, x19, test92
    c.addi x15, 0x1
test92:
    li x17, 0xe22e4d2c
    li x18, 0xd707d030
    .word 0x6528a9d7    #pv.sub.div2 x19, x17, x18
    li x20, 0x05933e7e
    beq x20, x19, test93
    c.addi x15, 0x1
test93:
    li x17, 0xd2a0ab24
    li x18, 0xb7313266
    .word 0x6528a9d7    #pv.sub.div2 x19, x17, x18
    li x20, 0x0db73c5f
    beq x20, x19, test94
    c.addi x15, 0x1
test94:
    li x17, 0x421fcb78
    li x18, 0x50d96dfb
    .word 0x6528a9d7    #pv.sub.div2 x19, x17, x18
    li x20, 0x78a32ebe
    beq x20, x19, test95
    c.addi x15, 0x1
test95:
    li x17, 0x07690ee7
    li x18, 0x4d704c3f
    .word 0x6528a9d7    #pv.sub.div2 x19, x17, x18
    li x20, 0x5cfc6154
    beq x20, x19, test96
    c.addi x15, 0x1
test96:
    li x17, 0xef6d5d16
    li x18, 0xa1357fb6
    .word 0x6528a9d7    #pv.sub.div2 x19, x17, x18
    li x20, 0x271c6eb0
    beq x20, x19, test97
    c.addi x15, 0x1
#tests97-102 test the pv.sub.div4 instruction. values loaded in and compared to are expected output values
#pv.sub.div4 is of the form "pv.sub.div4 rD, rs1, rs2". rD[31:16] = (rs1[31:16] - rs2[31:16])>>2
#rD [15:0] = (rs1[15:0] - rs2[15:0])>>2
test97:
    li x17, 0x9acbbae8
    li x18, 0x864b1016
    .word 0x6528c9d7    #pv.sub.div4 x19, x17, x18
    li x20, 0x05202ab4
    beq x20, x19, test98
    c.addi x15, 0x1
test98:
    li x17, 0x7d16ce4a
    li x18, 0x1a39f5ed
    .word 0x6528c9d7    #pv.sub.div4 x19, x17, x18
    li x20, 0x18b73617
    beq x20, x19, test99
    c.addi x15, 0x1
test99:
    li x17, 0x8c067ac4
    li x18, 0xb45b1be9
    .word 0x6528c9d7    #pv.sub.div4 x19, x17, x18
    li x20, 0x35ea17b6
    beq x20, x19, test100
    c.addi x15, 0x1
test100:
    li x17, 0xc88dc454
    li x18, 0xfae38066
    .word 0x6528c9d7    #pv.sub.div4 x19, x17, x18
    li x20, 0x336a10fb
    beq x20, x19, test101
    c.addi x15, 0x1
test101:
    li x17, 0x4145fcae
    li x18, 0x4466b932
    .word 0x6528c9d7    #pv.sub.div4 x19, x17, x18
    li x20, 0x3f3710df
    beq x20, x19, test102
    c.addi x15, 0x1
test102:
    li x17, 0xe8790ad6
    li x18, 0xeb8fa0c2
    .word 0x6528c9d7    #pv.sub.div4 x19, x17, x18
    li x20, 0x3f3a1a85
    beq x20, x19, test103
    c.addi x15, 0x1
#tests103-108 test the pv.sub.div8 instruction. values loaded in and compared to are expected output values
#pv.sub.div8 is of the form "pv.sub.div8 rD, rs1, rs2". rD[31:16] = (rs1[31:16] - rs2[31:16])>>3
#rD [15:0] = (rs1[15:0] - rs2[15:0])>>3
test103:
    li x17, 0xd9827dbe
    li x18, 0xa07767f4
    .word 0x6528e9d7    #pv.sub.div8 x19, x17, x18
    li x20, 0x072102b9
    beq x20, x19, test104
    c.addi x15, 0x1
test104:
    li x17, 0x1c6c1752
    li x18, 0x1ed81a7e
    .word 0x6528e9d7    #pv.sub.div8 x19, x17, x18
    li x20, 0x1fb21f9a
    beq x20, x19, test105
    c.addi x15, 0x1
test105:
    li x17, 0x1ef8926f
    li x18, 0x5e33d573
    .word 0x6528e9d7    #pv.sub.div8 x19, x17, x18
    li x20, 0x1818179f
    beq x20, x19, test106
    c.addi x15, 0x1
test106:
    li x17, 0x2da3a6a8
    li x18, 0x315abce2
    .word 0x6528e9d7    #pv.sub.div8 x19, x17, x18
    li x20, 0x1f891d38
    beq x20, x19, test107
    c.addi x15, 0x1
test107:
    li x17, 0xdf01e292
    li x18, 0xfd537fba
    .word 0x6528e9d7    #pv.sub.div8 x19, x17, x18
    li x20, 0x1c350c5b
    beq x20, x19, test108
    c.addi x15, 0x1
test108:
    li x17, 0x4ab407b2
    li x18, 0xd8cf4e64
    .word 0x6528e9d7    #pv.sub.div8 x19, x17, x18
    li x20, 0x0e3c1729
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
