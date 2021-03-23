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
#tests1-6 test the pv.min.h instruction. values loaded in and compared to are expected output values
#pv.min.h is of the form "pv.min.h rD, rs1, rs2". rD[31:16] = (rs1[31:16] < rs2[31:16]) ? rs1[31:16] : rs2[31:16]
#rD[15:0] = (rs1[15:0] < rs2[15:0]) ? rs1[15:0] : rs2[15:0]
#Note: this operation is signed
test1:
    li x17, 0x50d528e5
    li x18, 0xd2cf7173
    pv.min.h x19, x17, x18
    li x20, 0xd2cf28e5
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0xa3c77bc1
    li x18, 0xb3d90cf0
    pv.min.h x19, x17, x18
    li x20, 0xa3c70cf0
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0xb86f7dae
    li x18, 0x8c185ca0
    pv.min.h x19, x17, x18
    li x20, 0x8c185ca0
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x48ffc231
    li x18, 0x1f1d5987
    pv.min.h x19, x17, x18
    li x20, 0x1f1dc231
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0x8777da38
    li x18, 0x3040219e
    pv.min.h x19, x17, x18
    li x20, 0x8777da38
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x0a0202d8
    li x18, 0x5f83ca63
    pv.min.h x19, x17, x18
    li x20, 0x0a02ca63
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.min.sc.h instruction. values loaded in and compared to are expected output values
#pv.min.sc.h is of the form "pv.min.sc.h rD, rs1, rs2". rD[31:16] = (rs1[31:16] < rs2[15:0]) ? rs1[31:16] : rs2[15:0]
#rD[15:0] = (rs1[15:0] < rs2[15:0]) ? rs1[15:0] : rs2[15:0]
#Note: this operation is signed
test7:
    li x17, 0xe4c71d90
    li x18, 0x2c90fe3f
    pv.min.sc.h x19, x17, x18
    li x20, 0xe4c7fe3f
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0xd9f43272
    li x18, 0x74cbad98
    pv.min.sc.h x19, x17, x18
    li x20, 0xad98ad98
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x2930b92c
    li x18, 0xc4282e63
    pv.min.sc.h x19, x17, x18
    li x20, 0x2930b92c
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0x5b3b8e29
    li x18, 0xff8d069e
    pv.min.sc.h x19, x17, x18
    li x20, 0x069e8e29
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0x0e946b49
    li x18, 0x86b1c07d
    pv.min.sc.h x19, x17, x18
    li x20, 0xc07dc07d
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x4f75555c
    li x18, 0xd5a1db0d
    pv.min.sc.h x19, x17, x18
    li x20, 0xdb0ddb0d
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.min.sci.h instruction. values loaded in and compared to are expected output values
#pv.min.sci.h is of the form "pv.min.sci.h rD, rs1, Imm6". rD[31:16] = (rs1[31:16] < Imm6) ? rs1[31:16] : Imm6
#rD[15:0] = (rs1[15:0] < Imm6) ? rs1[15:0] : Imm6
#Note: this operation is signed
test13:
    li x17, 0xb6dcd8fd
    pv.min.sci.h x19, x17, -10
    li x20, 0xb6dcd8fd
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0xf5102b91
    pv.min.sci.h x19, x17, 31
    li x20, 0xf510001f
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0x837c1963
    pv.min.sci.h x19, x17, -1
    li x20, 0x837cffff
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0x311e6bac
    pv.min.sci.h x19, x17, 6
    li x20, 0x00060006
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x49c63a96
    pv.min.sci.h x19, x17, 18
    li x20, 0x00120012
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x4701d5c0
    pv.min.sci.h x19, x17, -27
    li x20, 0xffe5d5c0
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.min.b instruction. values loaded in and compared to are expected output values
#pv.min.b is of the form "pv.min.b rD, rs1, rs2". rD[31:24] = (rs1[31:24] < rs2[31:24]) ? rs1[31:24] : rs2[31:24],
#rD[23:16] = (rs1[23:16] < rs2[23:16]) ? rs1[23:16] : rs2[23:16], rD[15:8] = (rs1[15:8] < rs2[15:8]) ? rs1[15:8] : rs2[15:8]
#rD[7:0] = (rs1[7:0] < rs2[7:0]) ? rs1[7:0] : rs2[7:0]
#Note: this operation is signed
test19:
    li x17, 0xab5477c6
    li x18, 0x70948c7a
    pv.min.b x19, x17, x18
    li x20, 0xab948cc6
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x223b89be
    li x18, 0xe26ed5c8
    pv.min.b x19, x17, x18
    li x20, 0xe23b89be
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0xfc41fbe7
    li x18, 0xeeff784e
    pv.min.b x19, x17, x18
    li x20, 0xeefffbe7
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0xf0eb7ef6
    li x18, 0x5308253a
    pv.min.b x19, x17, x18
    li x20, 0xf0eb25f6
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0x0c1d7592
    li x18, 0x4000d0f7
    pv.min.b x19, x17, x18
    li x20, 0x0c00d092
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0x535ee5af
    li x18, 0xe9c4024b
    pv.min.b x19, x17, x18
    li x20, 0xe9c4e5af
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.min.sc.b instruction. values loaded in and compared to are expected output values
#pv.min.sc.b is of the form "pv.min.sc.b rD, rs1, rs2". rD[31:24] = (rs1[31:24] < rs2[7:0]) ? rs1[31:24] : rs2[7:0],
#rD[23:16] = (rs1[23:16] < rs2[7:0]) ? rs1[23:16] : rs2[7:0], rD[15:8] = (rs1[15:8] < rs2[7:0]) ? rs1[15:8] : rs2[7:0]
#rD[7:0] = (rs1[7:0] < rs2[7:0]) ? rs1[7:0] : rs2[7:0]
#Note: this operation is signed
test25:
    li x17, 0xb1ebd4aa
    li x18, 0xdf539b90
    pv.min.sc.b x19, x17, x18
    li x20, 0x90909090
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x8ae451b4
    li x18, 0x3392d130
    pv.min.sc.b x19, x17, x18
    li x20, 0x8ae430b4
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0x95cc319d
    li x18, 0x302de29a
    pv.min.sc.b x19, x17, x18
    li x20, 0x959a9a9a
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0xc7573c19
    li x18, 0x750b8b12
    pv.min.sc.b x19, x17, x18
    li x20, 0xc7121212
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0x79176d77
    li x18, 0x4d898d50
    pv.min.sc.b x19, x17, x18
    li x20, 0x50175050
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0x3be8009b
    li x18, 0xf93d44d7
    pv.min.sc.b x19, x17, x18
    li x20, 0xd7d7d79b
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.min.sci.b instruction. values loaded in and compared to are expected output values
#pv.min.sci.b is of the form "pv.min.sci.b rD, rs1, Imm6". rD[31:24] = (rs1[31:24] < Imm6) ? rs1[31:24] : Imm6,
#rD[23:16] = (rs1[23:16] < Imm6) ? rs1[23:16] : Imm6, rD[15:8] = (rs1[15:8] < Imm6) ? rs1[15:8] : Imm6
#rD[7:0] = (rs1[7:0] < Imm6) ? rs1[7:0] : Imm6
#Note: this operation is signed
test31:
    li x17, 0x8aa0713b
    pv.min.sci.b x19, x17, 5
    li x20, 0x8aa00505
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0xb85b2cb2
    pv.min.sci.b x19, x17, 31
    li x20, 0xb81f1fb2
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0xbd4d4004
    pv.min.sci.b x19, x17, -12
    li x20, 0xbdf4f4f4
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0x0b057a9c
    pv.min.sci.b x19, x17, -25
    li x20, 0xe7e7e79c
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x4bec8e74
    pv.min.sci.b x19, x17, 14
    li x20, 0x0eec8e0e
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0x88ace027
    pv.min.sci.b x19, x17, -2
    li x20, 0x88ace0fe
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.minu.h instruction. values loaded in and compared to are expected output values
#pv.minu.h is of the form "pv.minu.h rD, rs1, rs2". rD[31:16] = (rs1[31:16] < rs2[31:16]) ? rs1[31:16] : rs2[31:16]
#rD[15:0] = (rs1[15:0] < rs2[15:0]) ? rs1[15:0] : rs2[15:0]
#Note: this operation is unsigned
test37:
    li x17, 0x5ab31690
    li x18, 0xaa6f43e1
    pv.minu.h x19, x17, x18
    li x20, 0x5ab31690
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0xbb3bc8d0
    li x18, 0xe864027d
    pv.minu.h x19, x17, x18
    li x20, 0xbb3b027d
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0x3bd680c4
    li x18, 0xdd981fdc
    pv.minu.h x19, x17, x18
    li x20, 0x3bd61fdc
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0xceaa0cfa
    li x18, 0xa6363714
    pv.minu.h x19, x17, x18
    li x20, 0xa6360cfa
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0x5270bdd6
    li x18, 0xa7685441
    pv.minu.h x19, x17, x18
    li x20, 0x52705441
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0xd1477429
    li x18, 0x3ed73daa
    pv.minu.h x19, x17, x18
    li x20, 0x3ed73daa
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.minu.sc.h instruction. values loaded in and compared to are expected output values
#pv.minu.sc.h is of the form "pv.minu.sc.h rD, rs1, rs2". rD[31:16] = (rs1[31:16] < rs2[15:0]) ? rs1[31:16] : rs2[15:0]
#rD[15:0] = (rs1[15:0] < rs2[15:0]) ? rs1[15:0] : rs2[15:0]
#Note: this operation is unsigned
test43:
    li x17, 0xe4397d37
    li x18, 0x443e0dec
    pv.minu.sc.h x19, x17, x18
    li x20, 0x0dec0dec
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0xfe046649
    li x18, 0x501378e4
    pv.minu.sc.h x19, x17, x18
    li x20, 0x78e46649
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0xedc3e359
    li x18, 0x6bd34e43
    pv.minu.sc.h x19, x17, x18
    li x20, 0x4e434e43
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0x78a1e965
    li x18, 0x2da36eb5
    pv.minu.sc.h x19, x17, x18
    li x20, 0x6eb56eb5
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0xb47d65b9
    li x18, 0x0299555f
    pv.minu.sc.h x19, x17, x18
    li x20, 0x555f555f
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0x094fd1af
    li x18, 0xdb51eeff
    pv.minu.sc.h x19, x17, x18
    li x20, 0x094fd1af
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.minu.sci.h instruction. values loaded in and compared to are expected output values
#pv.minu.sci.h is of the form "pv.minu.sci.h rD, rs1, Imm6". rD[31:16] = (rs1[31:16] < Imm6) ? rs1[31:16] : Imm6
#rD[15:0] = (rs1[15:0] < Imm6) ? rs1[15:0] : Imm6
#Note: this operation is unsigned
test49:
    li x17, 0x36275f43
    pv.minu.sci.h x19, x17, 7
    li x20, 0x00070007
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0x5078d9e5
    pv.minu.sci.h x19, x17, 61
    li x20, 0x003d003d
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0xc6af7dff
    pv.minu.sci.h x19, x17, 46
    li x20, 0x002e002e
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0x8be32eec
    pv.minu.sci.h x19, x17, 19
    li x20, 0x00130013
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x00280c67
    pv.minu.sci.h x19, x17, 63
    li x20, 0x0028003f
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0xbb81dd79
    pv.minu.sci.h x19, x17, 31
    li x20, 0x001f001f
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.minu.b instruction. values loaded in and compared to are expected output values
#pv.minu.b is of the form "pv.minu.b rD, rs1, rs2". rD[31:24] = (rs1[31:24] < rs2[31:24]) ? rs1[31:24] : rs2[31:24],
#rD[23:16] = (rs1[23:16] < rs2[23:16]) ? rs1[23:16] : rs2[23:16], rD[15:8] = (rs1[15:8] < rs2[15:8]) ? rs1[15:8] : rs2[15:8]
#rD[7:0] = (rs1[7:0] < rs2[7:0]) ? rs1[7:0] : rs2[7:0]
#Note: this operation is unsigned
test55:
    li x17, 0xabcc4035
    li x18, 0xff2bf8e2
    pv.minu.b x19, x17, x18
    li x20, 0xab2b4035
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0xfacb134c
    li x18, 0x6c57317d
    pv.minu.b x19, x17, x18
    li x20, 0x6c57134c
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0x8ca1e2c2
    li x18, 0x14521a15
    pv.minu.b x19, x17, x18
    li x20, 0x14521a15
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0x50a23469
    li x18, 0xa3e1c74b
    pv.minu.b x19, x17, x18
    li x20, 0x50a2344b
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0xca8fe2cf
    li x18, 0x2b0d54d7
    pv.minu.b x19, x17, x18
    li x20, 0x2b0d54cf
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0xb20af4dc
    li x18, 0x0f883d09
    pv.minu.b x19, x17, x18
    li x20, 0x0f0a3d09
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.minu.sc.b instruction. values loaded in and compared to are expected output values
#pv.minu.sc.b is of the form "pv.minu.sc.b rD, rs1, rs2". rD[31:24] = (rs1[31:24] < rs2[7:0]) ? rs1[31:24] : rs2[7:0],
#rD[23:16] = (rs1[23:16] < rs2[7:0]) ? rs1[23:16] : rs2[7:0], rD[15:8] = (rs1[15:8] < rs2[7:0]) ? rs1[15:8] : rs2[7:0]
#rD[7:0] = (rs1[7:0] < rs2[7:0]) ? rs1[7:0] : rs2[7:0]
#Note: this operation is unsigned
test61:
    li x17, 0xe0c626a5
    li x18, 0x0bfc86bc
    pv.minu.sc.b x19, x17, x18
    li x20, 0xbcbc26a5
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x559d8487
    li x18, 0x834e39c2
    pv.minu.sc.b x19, x17, x18
    li x20, 0x559d8487
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0x05c1fd2a
    li x18, 0xb87766b9
    pv.minu.sc.b x19, x17, x18
    li x20, 0x05b9b92a
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0xced7df83
    li x18, 0x7a2b0046
    pv.minu.sc.b x19, x17, x18
    li x20, 0x46464646
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0xa7902b23
    li x18, 0x0250f5bc
    pv.minu.sc.b x19, x17, x18
    li x20, 0xa7902b23
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0xa997e80f
    li x18, 0x6441727b
    pv.minu.sc.b x19, x17, x18
    li x20, 0x7b7b7b0f
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.minu.sci.b instruction. values loaded in and compared to are expected output values
#pv.minu.sci.b is of the form "pv.minu.sci.b rD, rs1, Imm6". rD[31:24] = (rs1[31:24] < Imm6) ? rs1[31:24] : Imm6,
#rD[23:16] = (rs1[23:16] < Imm6) ? rs1[23:16] : Imm6, rD[15:8] = (rs1[15:8] < Imm6) ? rs1[15:8] : Imm6
#rD[7:0] = (rs1[7:0] < Imm6) ? rs1[7:0] : Imm6
#Note: this operation is unsigned
test67:
    li x17, 0xdc285752
    pv.minu.sci.b x19, x17, 45
    li x20, 0x2d282d2d
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0xdf0278d8
    pv.minu.sci.b x19, x17, 8
    li x20, 0x08020808
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0x32b8fc31
    pv.minu.sci.b x19, x17, 63
    li x20, 0x323f3f31
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x35b3cb9e
    pv.minu.sci.b x19, x17, 15
    li x20, 0x0f0f0f0f
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0x2b81c895
    pv.minu.sci.b x19, x17, 28
    li x20, 0x1c1c1c1c
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0x2451b6da
    pv.minu.sci.b x19, x17, 41
    li x20, 0x24292929
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
