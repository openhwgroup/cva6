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
#tests1-6 test the pv.max.h instruction. values loaded in and compared to are expected output values
#pv.max.h is of the form "pv.max.h rD, rs1, rs2". rD[31:16] = (rs1[31:16] < rs2[31:16]) ? rs1[31:16] : rs2[31:16]
#rD[15:0] = (rs1[15:0] < rs2[15:0]) ? rs1[15:0] : rs2[15:0]
#Note: this operation is signed
test1:
    li x17, 0xa5bdf218
    li x18, 0x9b1f75fd
    pv.max.h x19, x17, x18
    li x20, 0xa5bd75fd
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x485e8614
    li x18, 0x20e7e312
    pv.max.h x19, x17, x18
    li x20, 0x485ee312
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0x8c5b6b5c
    li x18, 0x1cef5501
    pv.max.h x19, x17, x18
    li x20, 0x1cef6b5c
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x5111dc0e
    li x18, 0xf9be2fc4
    pv.max.h x19, x17, x18
    li x20, 0x51112fc4
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0x0665f815
    li x18, 0xf3af5859
    pv.max.h x19, x17, x18
    li x20, 0x06655859
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x008be78e
    li x18, 0x2461aa6b
    pv.max.h x19, x17, x18
    li x20, 0x2461e78e
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.max.sc.h instruction. values loaded in and compared to are expected output values
#pv.max.sc.h is of the form "pv.max.sc.h rD, rs1, rs2". rD[31:16] = (rs1[31:16] < rs2[15:0]) ? rs1[31:16] : rs2[15:0]
#rD[15:0] = (rs1[15:0] < rs2[15:0]) ? rs1[15:0] : rs2[15:0]
#Note: this operation is signed
test7:
    li x17, 0x0e61cdd1
    li x18, 0xca577cbe
    pv.max.sc.h x19, x17, x18
    li x20, 0x7cbe7cbe
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x05c70c67
    li x18, 0x5bae2205
    pv.max.sc.h x19, x17, x18
    li x20, 0x22052205
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0xa4bb5388
    li x18, 0x451a3a51
    pv.max.sc.h x19, x17, x18
    li x20, 0x3a515388
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0x6a80a0bf
    li x18, 0x6fb32d2c
    pv.max.sc.h x19, x17, x18
    li x20, 0x6a802d2c
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0x06af9f11
    li x18, 0xd6b2d71e
    pv.max.sc.h x19, x17, x18
    li x20, 0x06afd71e
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x23976964
    li x18, 0xa6e6c709
    pv.max.sc.h x19, x17, x18
    li x20, 0x23976964
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.max.sci.h instruction. values loaded in and compared to are expected output values
#pv.max.sci.h is of the form "pv.max.sci.h rD, rs1, Imm6". rD[31:16] = (rs1[31:16] < Imm6) ? rs1[31:16] : Imm6
#rD[15:0] = (rs1[15:0] < Imm6) ? rs1[15:0] : Imm6
#Note: this operation is signed
test13:
    li x17, 0x68f98d40
    pv.max.sci.h x19, x17, -31
    li x20, 0x68f9ffe1
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0x632ccde0
    pv.max.sci.h x19, x17, 4
    li x20, 0x632c0004
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0xe388c3c2
    pv.max.sci.h x19, x17, 12
    li x20, 0x000c000c
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0x5e5e4cc1
    pv.max.sci.h x19, x17, -8
    li x20, 0x5e5e4cc1
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x1a9e4b0b
    pv.max.sci.h x19, x17, 25
    li x20, 0x1a9e4b0b
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0xeb583e8e
    pv.max.sci.h x19, x17, -20
    li x20, 0xffec3e8e
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.max.b instruction. values loaded in and compared to are expected output values
#pv.max.b is of the form "pv.max.b rD, rs1, rs2". rD[31:24] = (rs1[31:24] < rs2[31:24]) ? rs1[31:24] : rs2[31:24],
#rD[23:16] = (rs1[23:16] < rs2[23:16]) ? rs1[23:16] : rs2[23:16], rD[15:8] = (rs1[15:8] < rs2[15:8]) ? rs1[15:8] : rs2[15:8]
#rD[7:0] = (rs1[7:0] < rs2[7:0]) ? rs1[7:0] : rs2[7:0]
#Note: this operation is signed
test19:
    li x17, 0x57d5ba10
    li x18, 0xb8fb99fe
    pv.max.b x19, x17, x18
    li x20, 0x57fbba10
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x53643b08
    li x18, 0x45ddde21
    pv.max.b x19, x17, x18
    li x20, 0x53643b21
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0x74f545ab
    li x18, 0x5c6001ef
    pv.max.b x19, x17, x18
    li x20, 0x746045ef
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0x1d4130e4
    li x18, 0x291c785d
    pv.max.b x19, x17, x18
    li x20, 0x2941785d
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0xa1f3d698
    li x18, 0x5ec7e5bf
    pv.max.b x19, x17, x18
    li x20, 0x5ef3e5bf
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0xffd13622
    li x18, 0x6583ae84
    pv.max.b x19, x17, x18
    li x20, 0x65d13622
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.max.sc.b instruction. values loaded in and compared to are expected output values
#pv.max.sc.b is of the form "pv.max.sc.b rD, rs1, rs2". rD[31:24] = (rs1[31:24] < rs2[7:0]) ? rs1[31:24] : rs2[7:0],
#rD[23:16] = (rs1[23:16] < rs2[7:0]) ? rs1[23:16] : rs2[7:0], rD[15:8] = (rs1[15:8] < rs2[7:0]) ? rs1[15:8] : rs2[7:0]
#rD[7:0] = (rs1[7:0] < rs2[7:0]) ? rs1[7:0] : rs2[7:0]
#Note: this operation is signed
test25:
    li x17, 0xe8e06d5e
    li x18, 0xd2a78b47
    pv.max.sc.b x19, x17, x18
    li x20, 0x47476d5e
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x8b61d990
    li x18, 0x1130c5c2
    pv.max.sc.b x19, x17, x18
    li x20, 0xc261d9c2
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0xb7e54cfd
    li x18, 0x34db4908
    pv.max.sc.b x19, x17, x18
    li x20, 0x08084c08
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0xbeae9182
    li x18, 0xc6b8a0e5
    pv.max.sc.b x19, x17, x18
    li x20, 0xe5e5e5e5
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0x4ae0d93b
    li x18, 0x07161363
    pv.max.sc.b x19, x17, x18
    li x20, 0x63636363
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0x8d712b11
    li x18, 0x4a119ae2
    pv.max.sc.b x19, x17, x18
    li x20, 0xe2712b11
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.max.sci.b instruction. values loaded in and compared to are expected output values
#pv.max.sci.b is of the form "pv.max.sci.b rD, rs1, Imm6". rD[31:24] = (rs1[31:24] < Imm6) ? rs1[31:24] : Imm6,
#rD[23:16] = (rs1[23:16] < Imm6) ? rs1[23:16] : Imm6, rD[15:8] = (rs1[15:8] < Imm6) ? rs1[15:8] : Imm6
#rD[7:0] = (rs1[7:0] < Imm6) ? rs1[7:0] : Imm6
#Note: this operation is signed
test31:
    li x17, 0x5d500f41
    pv.max.sci.b x19, x17, 31
    li x20, 0x5d501f41
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0x47cb1a44
    pv.max.sci.b x19, x17, -28
    li x20, 0x47e41a44
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0x4c1de3f0
    pv.max.sci.b x19, x17, 7
    li x20, 0x4c1d0707
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0x23673031
    pv.max.sci.b x19, x17, -15
    li x20, 0x23673031
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x5e7210ca
    pv.max.sci.b x19, x17, 3
    li x20, 0x5e721003
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0xb96e9513
    pv.max.sci.b x19, x17, -5
    li x20, 0xfb6efb13
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.maxu.h instruction. values loaded in and compared to are expected output values
#pv.maxu.h is of the form "pv.maxu.h rD, rs1, rs2". rD[31:16] = (rs1[31:16] < rs2[31:16]) ? rs1[31:16] : rs2[31:16]
#rD[15:0] = (rs1[15:0] < rs2[15:0]) ? rs1[15:0] : rs2[15:0]
#Note: this operation is unsigned
test37:
    li x17, 0x137e84de
    li x18, 0xf6570ec4
    pv.maxu.h x19, x17, x18
    li x20, 0xf65784de
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0x2fd5e84d
    li x18, 0x48b8a287
    pv.maxu.h x19, x17, x18
    li x20, 0x48b8e84d
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0xb797125b
    li x18, 0x1da8fe26
    pv.maxu.h x19, x17, x18
    li x20, 0xb797fe26
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x04237026
    li x18, 0x6a3c8d9b
    pv.maxu.h x19, x17, x18
    li x20, 0x6a3c8d9b
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0xd751f4c9
    li x18, 0x954ca8c3
    pv.maxu.h x19, x17, x18
    li x20, 0xd751f4c9
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0x7748fe61
    li x18, 0x81d7be34
    pv.maxu.h x19, x17, x18
    li x20, 0x81d7fe61
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.maxu.sc.h instruction. values loaded in and compared to are expected output values
#pv.maxu.sc.h is of the form "pv.maxu.sc.h rD, rs1, rs2". rD[31:16] = (rs1[31:16] < rs2[15:0]) ? rs1[31:16] : rs2[15:0]
#rD[15:0] = (rs1[15:0] < rs2[15:0]) ? rs1[15:0] : rs2[15:0]
#Note: this operation is unsigned
test43:
    li x17, 0xc6475aaa
    li x18, 0xf4e3e76c
    pv.maxu.sc.h x19, x17, x18
    li x20, 0xe76ce76c
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0x494897ed
    li x18, 0x55817edb
    pv.maxu.sc.h x19, x17, x18
    li x20, 0x7edb97ed
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0xe41f4be2
    li x18, 0x57c005fd
    pv.maxu.sc.h x19, x17, x18
    li x20, 0xe41f4be2
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0xbc3a28b5
    li x18, 0xd1d80561
    pv.maxu.sc.h x19, x17, x18
    li x20, 0xbc3a28b5
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0xec7d6ec5
    li x18, 0x1a85cbf1
    pv.maxu.sc.h x19, x17, x18
    li x20, 0xec7dcbf1
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0x2a76bb1a
    li x18, 0xd2081774
    pv.maxu.sc.h x19, x17, x18
    li x20, 0x2a76bb1a
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.maxu.sci.h instruction. values loaded in and compared to are expected output values
#pv.maxu.sci.h is of the form "pv.maxu.sci.h rD, rs1, Imm6". rD[31:16] = (rs1[31:16] < Imm6) ? rs1[31:16] : Imm6
#rD[15:0] = (rs1[15:0] < Imm6) ? rs1[15:0] : Imm6
#Note: this operation is unsigned
test49:
    li x17, 0xa8df8a3f
    pv.maxu.sci.h x19, x17, 7
    li x20, 0xa8df8a3f
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0xa5a3805a
    pv.maxu.sci.h x19, x17, 25
    li x20, 0xa5a3805a
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0x0408f5de
    pv.maxu.sci.h x19, x17, 63
    li x20, 0x0408f5de
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0x487d0383
    pv.maxu.sci.h x19, x17, 13
    li x20, 0x487d0383
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x426e0022
    pv.maxu.sci.h x19, x17, 48
    li x20, 0x426e0030
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0x6e958c26
    pv.maxu.sci.h x19, x17, 37
    li x20, 0x6e958c26
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.maxu.b instruction. values loaded in and compared to are expected output values
#pv.maxu.b is of the form "pv.maxu.b rD, rs1, rs2". rD[31:24] = (rs1[31:24] < rs2[31:24]) ? rs1[31:24] : rs2[31:24],
#rD[23:16] = (rs1[23:16] < rs2[23:16]) ? rs1[23:16] : rs2[23:16], rD[15:8] = (rs1[15:8] < rs2[15:8]) ? rs1[15:8] : rs2[15:8]
#rD[7:0] = (rs1[7:0] < rs2[7:0]) ? rs1[7:0] : rs2[7:0]
#Note: this operation is unsigned
test55:
    li x17, 0x0a9c9e0f
    li x18, 0xca1fa63f
    pv.maxu.b x19, x17, x18
    li x20, 0xca9ca63f
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0xfa8225cc
    li x18, 0xe6653139
    pv.maxu.b x19, x17, x18
    li x20, 0xfa8231cc
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0x4905989c
    li x18, 0x330a6231
    pv.maxu.b x19, x17, x18
    li x20, 0x490a989c
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0xefa420af
    li x18, 0x216abca5
    pv.maxu.b x19, x17, x18
    li x20, 0xefa4bcaf
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0x52446d60
    li x18, 0x64e53210
    pv.maxu.b x19, x17, x18
    li x20, 0x64e56d60
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0x6667f26c
    li x18, 0xd225475c
    pv.maxu.b x19, x17, x18
    li x20, 0xd267f26c
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.maxu.sc.b instruction. values loaded in and compared to are expected output values
#pv.maxu.sc.b is of the form "pv.maxu.sc.b rD, rs1, rs2". rD[31:24] = (rs1[31:24] < rs2[7:0]) ? rs1[31:24] : rs2[7:0],
#rD[23:16] = (rs1[23:16] < rs2[7:0]) ? rs1[23:16] : rs2[7:0], rD[15:8] = (rs1[15:8] < rs2[7:0]) ? rs1[15:8] : rs2[7:0]
#rD[7:0] = (rs1[7:0] < rs2[7:0]) ? rs1[7:0] : rs2[7:0]
#Note: this operation is unsigned
test61:
    li x17, 0xa2ef7541
    li x18, 0xefc3e173
    pv.maxu.sc.b x19, x17, x18
    li x20, 0xa2ef7573
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x01129349
    li x18, 0x30fe7d05
    pv.maxu.sc.b x19, x17, x18
    li x20, 0x05129349
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0x695f33e5
    li x18, 0x94cf9a4d
    pv.maxu.sc.b x19, x17, x18
    li x20, 0x695f4de5
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0x1824569e
    li x18, 0xa44a5129
    pv.maxu.sc.b x19, x17, x18
    li x20, 0x2929569e
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0x13603783
    li x18, 0xbaffa7b8
    pv.maxu.sc.b x19, x17, x18
    li x20, 0xb8b8b8b8
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0x823f183d
    li x18, 0xddabb51e
    pv.maxu.sc.b x19, x17, x18
    li x20, 0x823f1e3d
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.maxu.sci.b instruction. values loaded in and compared to are expected output values
#pv.maxu.sci.b is of the form "pv.maxu.sci.b rD, rs1, Imm6". rD[31:24] = (rs1[31:24] < Imm6) ? rs1[31:24] : Imm6,
#rD[23:16] = (rs1[23:16] < Imm6) ? rs1[23:16] : Imm6, rD[15:8] = (rs1[15:8] < Imm6) ? rs1[15:8] : Imm6
#rD[7:0] = (rs1[7:0] < Imm6) ? rs1[7:0] : Imm6
#Note: this operation is unsigned
test67:
    li x17, 0xe127d500
    pv.maxu.sci.b x19, x17, 8
    li x20, 0xe127d508
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0xb2555556
    pv.maxu.sci.b x19, x17, 25
    li x20, 0xb2555556
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0x50ef49de
    pv.maxu.sci.b x19, x17, 37
    li x20, 0x50ef49de
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x386221dd
    pv.maxu.sci.b x19, x17, 54
    li x20, 0x386236dd
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0x9c24b7e7
    pv.maxu.sci.b x19, x17, 63
    li x20, 0x9c3fb7e7
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0x809e5f46
    pv.maxu.sci.b x19, x17, 12
    li x20, 0x809e5f46
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
