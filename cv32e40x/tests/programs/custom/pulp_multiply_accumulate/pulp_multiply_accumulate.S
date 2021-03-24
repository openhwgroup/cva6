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
#tests all multiply-accumulate instructions. NOTE: value of register x15 at the end of the test is the error count
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
#tests1-6 test the p.mac instruction. values loaded in and compared to are expected output values
#p.mac instruction is of format "p.mac rD, rs1, rs2". rD = rD + rs1 * rs2
test1:
    li x18, 0xe8a5056b
    li x20, 0x2e05bb8c
    li x21, 0x9ac17ad0
    p.mac x18, x20, x21
    li x19, 0xa53a1f2b
    beq x18, x19, test2
    c.addi x15, 0x1
test2:
    li x18, 0xf474bbd5
    li x20, 0xbb06dba8
    li x21, 0x1331adce
    p.mac x18, x20, x21
    li x19, 0x99920505
    beq x18, x19, test3
    c.addi x15, 0x1
test3:
    li x18, 0xa5fd60b4
    li x20, 0xe56cc495
    li x21, 0x26455ded
    p.mac x18, x20, x21
    li x19, 0xa9427fa5
    beq x18, x19, test4
    c.addi x15, 0x1
test4:
    li x18, 0xd3b769ab
    li x20, 0xa693f8ed
    li x21, 0x98649434
    p.mac x18, x20, x21
    li x19, 0x2a42fdcf
    beq x18, x19, test5
    c.addi x15, 0x1
test5:
    li x18, 0x79fe6a01
    li x20, 0xabeae759
    li x21, 0x37c34582
    p.mac x18, x20, x21
    li x19, 0x6f6de233
    beq x18, x19, test6
    c.addi x15, 0x1
test6:
    li x18, 0xe2cff4bc
    li x20, 0x698f518e
    li x21, 0xff0a0a1f
    p.mac x18, x20, x21
    li x19, 0xe5e660ee
    beq x18, x19, test7
    c.addi x15, 0x1
#tests7-12 test the p.msu instruction. values loaded in and compared to are expected output values
#p.msu instruction is of format "p.msu rD, rs1, rs2". rD = rD - rs1 * rs2
test7:
    li x18, 0x9a213505
    li x20, 0x91619407
    li x21, 0xc6ee52b8
    p.msu x18, x20, x21
    li x19, 0xd21291fd
    beq x18, x19, test8
    c.addi x15, 0x1
test8:
    li x18, 0x64a7d13a
    li x20, 0x568985a7
    li x21, 0x58c041b1
    p.msu x18, x20, x21
    li x19, 0xff6301c3
    beq x18, x19, test9
    c.addi x15, 0x1
test9:
    li x18, 0x3166c1df
    li x20, 0xaaa824bc
    li x21, 0xfbe9e46d
    p.msu x18, x20, x21
    li x19, 0x03fbadd3
    beq x18, x19, test10
    c.addi x15, 0x1
test10:
    li x18, 0x15aca170
    li x20, 0xceda0bed
    li x21, 0xbf3be51f
    p.msu x18, x20, x21
    li x19, 0x69fb2ebd
    beq x18, x19, test11
    c.addi x15, 0x1
test11:
    li x18, 0x6316050a
    li x20, 0x6ea40095
    li x21, 0x8a5fbb09
    p.msu x18, x20, x21
    li x19, 0x299a28cd
    beq x18, x19, test12
    c.addi x15, 0x1
test12:
    li x18, 0xb3d3cae2
    li x20, 0x0478637a
    li x21, 0x2d2dc58f
    p.msu x18, x20, x21
    li x19, 0xa19557bc
    beq x18, x19, test13
    c.addi x15, 0x1
#tests13-18 test the p.muls instruction. values loaded in and compared to are expected output values
#p.muls instruction is of format "p.muls rD, rs1, rs2". rD[31:0] = Sext(rs1[15:0]) * Sext(rs2[15:0])
test13:
    li x20, 0x1efce4a5
    li x21, 0xa6529f8c
    p.muls x18, x20, x21
    li x19, 0x0a4e853c
    beq x18, x19, test14
    c.addi x15, 0x1
test14:
    li x20, 0xaf5cbf12
    li x21, 0x6d2c1168
    p.muls x18, x20, x21
    li x19, 0xfb95d150
    beq x18, x19, test15
    c.addi x15, 0x1
test15:
    li x20, 0x91ef944b
    li x21, 0x12d44ba4
    p.muls x18, x20, x21
    li x19, 0xe02cf90c
    beq x18, x19, test16
    c.addi x15, 0x1
test16:
    li x20, 0x011349f4
    li x21, 0x388b7224
    p.muls x18, x20, x21
    li x19, 0x20f90e50
    beq x18, x19, test17
    c.addi x15, 0x1
test17:
    li x20, 0x3f59a8a1
    li x21, 0xaa5e39a7
    p.muls x18, x20, x21
    li x19, 0xec52da07
    beq x18, x19, test18
    c.addi x15, 0x1
test18:
    li x20, 0x73107229
    li x21, 0x5e5604cd
    p.muls x18, x20, x21
    li x19, 0x02240ed5
    beq x18, x19, test19
    c.addi x15, 0x1
#tests19-24 test the p.mulhhs instruction. values loaded in and compared to are expected output values
#p.mulhhs instruction is of format "p.mulhhs rD, rs1, rs2". rD[31:0] = Sext(rs1[31:15]) * Sext(rs2[31:15])
test19:
    li x20, 0x47186154
    li x21, 0x81300f73
    p.mulhhs x18, x20, x21
    li x19, 0xdcc86c80
    beq x18, x19, test20
    c.addi x15, 0x1
test20:
    li x20, 0x57517955
    li x21, 0xee33a51c
    p.mulhhs x18, x20, x21
    li x19, 0xf9edb323
    beq x18, x19, test21
    c.addi x15, 0x1
test21:
    li x20, 0x3a30c494
    li x21, 0x161c6fa5
    p.mulhhs x18, x20, x21
    li x19, 0x05067d40
    beq x18, x19, test22
    c.addi x15, 0x1
test22:
    li x20, 0x73d13103
    li x21, 0x7c3c4d6f
    p.mulhhs x18, x20, x21
    li x19, 0x383460fc
    beq x18, x19, test23
    c.addi x15, 0x1
test23:
    li x20, 0x8abe0f9f
    li x21, 0xdf26fe0d
    p.mulhhs x18, x20, x21
    li x19, 0x0f0c1a34
    beq x18, x19, test24
    c.addi x15, 0x1
test24:
    li x20, 0x468bf1d2
    li x21, 0x0fc23c8b
    p.mulhhs x18, x20, x21
    li x19, 0x04579a56
    beq x18, x19, test25
    c.addi x15, 0x1
#tests25-30 test the p.mulsN instruction. values loaded in and compared to are expected output values
#p.mulsN instruction is of format "p.mulsN rD, rs1, rs2, ls3". rD[31:0] = (Sext(rs1[15:0]) * Sext(rs2[15:0])) >>> ls3
test25:
    li x20, 0x74331682
    li x21, 0x0aa1f5a9
    p.mulsN x18, x20, x21, 7
    li x19, 0xfffe2e8b
    beq x18, x19, test26
    c.addi x15, 0x1
test26:
    li x20, 0xde4f9245
    li x21, 0x1605a4a9
    p.mulsN x18, x20, x21, 3
    li x19, 0x04e4d871
    beq x18, x19, test27
    c.addi x15, 0x1
test27:
    li x20, 0xd91414bd
    li x21, 0xa3970907
    p.mulsN x18, x20, x21, 8
    li x19, 0x0000bb36
    beq x18, x19, test28
    c.addi x15, 0x1
test28:
    li x20, 0x28d31573
    li x21, 0x3ae29717
    p.mulsN x18, x20, x21, 0x19
    li x19, 0xfffffffb
    beq x18, x19, test29
    c.addi x15, 0x1
test29:
    li x20, 0x30c868ca
    li x21, 0x7c404007
    p.mulsN x18, x20, x21, 0xf
    li x19, 0x0000346a
    beq x18, x19, test30
    c.addi x15, 0x1
test30:
    li x20, 0x26d2600c
    li x21, 0x729daf0f
    p.mulsN x18, x20, x21, 0xa
    li x19, 0xfff86875
    beq x18, x19, test31
    c.addi x15, 0x1
#tests31-36 test the p.mulhhsN instruction. values loaded in and compared to are expected output values
#p.mulhhsN instruction is of format "p.mulhhsN rD, rs1, rs2, ls3". rD[31:0] = (Sext(rs1[31:15]) * Sext(rs2[31:15])) >>> ls3
test31:
    li x20, 0x47186154
    li x21, 0x81300f73
    p.mulhhsN x18, x20, x21, 6
    li x19, 0xff7321b2
    beq x18, x19, test32
    c.addi x15, 0x1
test32:
    li x20, 0x57517955
    li x21, 0xee33a51c
    p.mulhhsN x18, x20, x21, 9
    li x19, 0xfffcf6d9
    beq x18, x19, test33
    c.addi x15, 0x1
test33:
    li x20, 0x3a30c494
    li x21, 0x161c6fa5
    p.mulhhsN x18, x20, x21, 0x12
    li x19, 0x00000141
    beq x18, x19, test34
    c.addi x15, 0x1
test34:
    li x20, 0x73d13103
    li x21, 0x7c3c4d6f
    p.mulhhsN x18, x20, x21, 0x17
    li x19, 0x00000070
    beq x18, x19, test35
    c.addi x15, 0x1
test35:
    li x20, 0x8abe0f9f
    li x21, 0xdf26fe0d
    p.mulhhsN x18, x20, x21, 2
    li x19, 0x03c3068d
    beq x18, x19, test36
    c.addi x15, 0x1
test36:
    li x20, 0x468bf1d2
    li x21, 0x0fc23c8b
    p.mulhhsN x18, x20, x21, 9
    li x19, 0x00022bcd
    beq x18, x19, test37
    c.addi x15, 0x1
#tests37-42 test the p.mulsRN instruction. values loaded in and compared to are expected output values
#p.mulsRN instruction is of format "p.mulsRN rD, rs1, rs2, ls3". rD[31:0] = (Sext(rs1[15:0]) * Sext(rs2[15:0]) + 2^(ls3-1)) >>> ls3
test37:
    li x20, 0x645be558
    li x21, 0x62e5f55c
    p.mulsRN x18, x20, x21, 2
    li x19, 0x0046e8e8
    beq x18, x19, test38
    c.addi x15, 0x1
test38:
    li x20, 0x4635074b
    li x21, 0xe7c4c350
    p.mulsRN x18, x20, x21, 6
    li x19, 0xfff915a2
    beq x18, x19, test39
    c.addi x15, 0x1
test39:
    li x20, 0xfedb2992
    li x21, 0x2b9a5f93
    p.mulsRN x18, x20, x21, 0xf
    li x19, 0x00001f0a
    beq x18, x19, test40
    c.addi x15, 0x1
test40:
    li x20, 0xb0f25142
    li x21, 0xdd3234fa
    p.mulsRN x18, x20, x21, 8
    li x19, 0x0010d0c2
    beq x18, x19, test41
    c.addi x15, 0x1
test41:
    li x20, 0x02790358
    li x21, 0x6f13c02b
    p.mulsRN x18, x20, x21, 5
    li x19, 0xfff9547e
    beq x18, x19, test42
    c.addi x15, 0x1
test42:
    li x20, 0x2ee3bd6d
    li x21, 0xa7525b2a
    p.mulsRN x18, x20, x21, 0xb
    li x19, 0xfffd095a
    beq x18, x19, test43
    c.addi x15, 0x1
#tests43-48 test the p.mulhhsRN instruction. values loaded in and compared to are expected output values
#p.mulhhsRN instruction is of format "p.mulhhsRN rD, rs1, rs2, ls3". rD[31:0] = (Sext(rs1[31:15]) * Sext(rs2[31:15])) >>> ls3
test43:
    li x20, 0xd4d8f1cc
    li x21, 0x49d48c10
    p.mulhhsRN x18, x20, x21, 0xc
    li x19, 0xffff38de
    beq x18, x19, test44
    c.addi x15, 0x1
test44:
    li x20, 0x04c87470
    li x21, 0x9c7bc8b5
    p.mulhhsRN x18, x20, x21, 0x12
    li x19, 0xffffff89
    beq x18, x19, test45
    c.addi x15, 0x1
test45:
    li x20, 0xf05e71ec
    li x21, 0xd842481b
    p.mulhhsRN x18, x20, x21, 0x10
    li x19, 0x0000026d
    beq x18, x19, test46
    c.addi x15, 0x1
test46:
    li x20, 0x71abaa20
    li x21, 0x6475d3e0
    p.mulhhsRN x18, x20, x21, 3
    li x19, 0x059357e5
    beq x18, x19, test47
    c.addi x15, 0x1
test47:
    li x20, 0xa4f23563
    li x21, 0xa54cdf55
    p.mulhhsRN x18, x20, x21, 6
    li x19, 0x00810bc7
    beq x18, x19, test48
    c.addi x15, 0x1
test48:
    li x20, 0x3079b2b5
    li x21, 0xcb198c64
    p.mulhhsRN x18, x20, x21, 0x14
    li x19, 0xffffff60
    beq x18, x19, test49
    c.addi x15, 0x1
#tests49-54 test the p.mulu instruction. values loaded in and compared to are expected output values
#p.mulu instruction is of format "p.mulu rD, rs1, rs2". rD[31:0] = Zext(rs1[15:0]) * Zext(rs2[15:0])
test49:
    li x20, 0x76166875
    li x21, 0xdde8888b
    p.mulu x18, x20, x21
    li x19, 0x37b6df87
    beq x18, x19, test50
    c.addi x15, 0x1
test50:
    li x20, 0xd2562f8e
    li x21, 0xdb29c6c3
    p.mulu x18, x20, x21
    li x19, 0x24ec0d2a
    beq x18, x19, test51
    c.addi x15, 0x1
test51:
    li x20, 0xb24b4bbf
    li x21, 0x2acef5ae
    p.mulu x18, x20, x21
    li x19, 0x48b146d2
    beq x18, x19, test52
    c.addi x15, 0x1
test52:
    li x20, 0xdfc326dc
    li x21, 0x42ed13f0
    p.mulu x18, x20, x21
    li x19, 0x0306c240
    beq x18, x19, test53
    c.addi x15, 0x1
test53:
    li x20, 0x48b617d0
    li x21, 0xe5265d14
    p.mulu x18, x20, x21
    li x19, 0x08a86c40
    beq x18, x19, test54
    c.addi x15, 0x1
test54:
    li x20, 0x9f60f8c5
    li x21, 0xbac9e541
    p.mulu x18, x20, x21
    li x19, 0xdec76305
    beq x18, x19, test55
    c.addi x15, 0x1
#tests55-60 test the p.mulhhu instruction. values loaded in and compared to are expected output values
#p.mulhhu instruction is of format "p.mulhhu rD, rs1, rs2". rD[31:0] = Zext(rs1[31:15]) * Zext(rs2[31:15])
test55:
    li x20, 0xc3fb288f
    li x21, 0x2790adaf
    p.mulhhu x18, x20, x21
    li x19, 0x1e497a30
    beq x18, x19, test56
    c.addi x15, 0x1
test56:
    li x20, 0x663d5315
    li x21, 0x2d9709f3
    p.mulhhu x18, x20, x21
    li x19, 0x123506fb
    beq x18, x19, test57
    c.addi x15, 0x1
test57:
    li x20, 0x5c7ed832
    li x21, 0x315bf527
    p.mulhhu x18, x20, x21
    li x19, 0x11d4feca
    beq x18, x19, test58
    c.addi x15, 0x1
test58:
    li x20, 0xb97ecf47
    li x21, 0xc78d0ed6
    p.mulhhu x18, x20, x21
    li x19, 0x90971c66
    beq x18, x19, test59
    c.addi x15, 0x1
test59:
    li x20, 0x8967cd6d
    li x21, 0x7d583a7c
    p.mulhhu x18, x20, x21
    li x19, 0x43468668
    beq x18, x19, test60
    c.addi x15, 0x1
test60:
    li x20, 0xa077484b
    li x21, 0xe729d470
    p.mulhhu x18, x20, x21
    li x19, 0x90e5140f
    beq x18, x19, test61
    c.addi x15, 0x1
#tests61-66 test the p.muluN instruction. values loaded in and compared to are expected output values
#p.muluN instruction is of format "p.muluN rD, rs1, rs2, ls3". rD[31:0] = (Zext(rs1[15:0]) * Zext(rs2[15:0])) >> ls3
test61:
    li x20, 0x76166875
    li x21, 0xdde8888b
    p.muluN x18, x20, x21, 0xe
    li x19, 0x0000dedb
    beq x18, x19, test62
    c.addi x15, 0x1
test62:
    li x20, 0xd2562f8e
    li x21, 0xdb29c6c3
    p.muluN x18, x20, x21, 3
    li x19, 0x049d81a5
    beq x18, x19, test63
    c.addi x15, 0x1
test63:
    li x20, 0xb24b4bbf
    li x21, 0x2acef5ae
    p.muluN x18, x20, x21, 9
    li x19, 0x002458a3
    beq x18, x19, test64
    c.addi x15, 0x1
test64:
    li x20, 0xdfc326dc
    li x21, 0x42ed13f0
    p.muluN x18, x20, x21, 5
    li x19, 0x00183612
    beq x18, x19, test65
    c.addi x15, 0x1
test65:
    li x20, 0x48b617d0
    li x21, 0xe5265d14
    p.muluN x18, x20, x21, 0x12
    li x19, 0x0000022a
    beq x18, x19, test66
    c.addi x15, 0x1
test66:
    li x20, 0x9f60f8c5
    li x21, 0xbac9e541
    p.muluN x18, x20, x21, 1
    li x19, 0x6f63b182
    beq x18, x19, test67
    c.addi x15, 0x1
#tests67-72 test the p.mulhhuN instruction. values loaded in and compared to are expected output values
#p.mulhhuN instruction is of format "p.mulhhuN rD, rs1, rs2, ls3". rD[31:0] = (Zext(rs1[31:15]) * Zext(rs2[31:15])) >> ls3
test67:
    li x20, 0xc3fb288f
    li x21, 0x2790adaf
    p.mulhhuN x18, x20, x21, 0x1b
    li x19, 0x00000003
    beq x18, x19, test68
    c.addi x15, 0x1
test68:
    li x20, 0x663d5315
    li x21, 0x2d9709f3
    p.mulhhuN x18, x20, x21, 0xd
    li x19, 0x000091a8
    beq x18, x19, test69
    c.addi x15, 0x1
test69:
    li x20, 0x5c7ed832
    li x21, 0x315bf527
    p.mulhhuN x18, x20, x21, 7
    li x19, 0x0023a9fd
    beq x18, x19, test70
    c.addi x15, 0x1
test70:
    li x20, 0xb97ecf47
    li x21, 0xc78d0ed6
    p.mulhhuN x18, x20, x21, 1
    li x19, 0x484b8e33
    beq x18, x19, test71
    c.addi x15, 0x1
test71:
    li x20, 0x8967cd6d
    li x21, 0x7d583a7c
    p.mulhhuN x18, x20, x21, 5
    li x19, 0x021a3433
    beq x18, x19, test72
    c.addi x15, 0x1
test72:
    li x20, 0xa077484b
    li x21, 0xe729d470
    p.mulhhuN x18, x20, x21, 0xa
    li x19, 0x00243945
    beq x18, x19, test73
    c.addi x15, 0x1
#tests73-78 test the p.muluRN instruction. values loaded in and compared to are expected output values
#p.muluRN instruction is of format "p.muluRN rD, rs1, rs2, ls3". rD[31:0] = (Zext(rs1[15:0]) * Zext(rs2[15:0]) + 2^(ls3-1)) >> ls3
test73:
    li x20, 0x830e73b0
    li x21, 0x1eba9c18
    p.muluRN x18, x20, x21, 0xe
    li x19, 0x00011a28
    beq x18, x19, test74
    c.addi x15, 0x1
test74:
    li x20, 0x82345bf4
    li x21, 0x1b110ff1
    p.muluRN x18, x20, x21, 6
    li x19, 0x0016e773
    beq x18, x19, test75
    c.addi x15, 0x1
test75:
    li x20, 0xb8207aa3
    li x21, 0xfe75774f
    p.muluRN x18, x20, x21, 0x11
    li x19, 0x00001c94
    beq x18, x19, test76
    c.addi x15, 0x1
test76:
    li x20, 0x863deeb5
    li x21, 0x0cb19e03
    p.muluRN x18, x20, x21, 0xb
    li x19, 0x00126ad0
    beq x18, x19, test77
    c.addi x15, 0x1
test77:
    li x20, 0xd19fbf93
    li x21, 0x60c2ad03
    p.muluRN x18, x20, x21, 3
    li x19, 0x102f12b7
    beq x18, x19, test78
    c.addi x15, 0x1
test78:
    li x20, 0x93f10127
    li x21, 0x553b188d
    p.muluRN x18, x20, x21, 8
    li x19, 0x00001c4a
    beq x18, x19, test79
    c.addi x15, 0x1
#tests79-84 test the p.mulhhuRN instruction. values loaded in and compared to are expected output values
#p.mulhhuRN instruction is of format "p.mulhhuRN rD, rs1, rs2, ls3". rD[31:0] = (Zext(rs1[31:15]) * Zext(rs2[31:15])) >> ls3
test79:
    li x20, 0xe35855c5
    li x21, 0x4e4efe65
    p.mulhhuRN x18, x20, x21, 0xf
    li x19, 0x00008b14
    beq x18, x19, test80
    c.addi x15, 0x1
test80:
    li x20, 0x873f255e
    li x21, 0xfbcde5a9
    p.mulhhuRN x18, x20, x21, 1
    li x19, 0x4283893a
    beq x18, x19, test81
    c.addi x15, 0x1
test81:
    li x20, 0x29498247
    li x21, 0x6361c24c
    p.mulhhuRN x18, x20, x21, 0x12
    li x19, 0x00000402
    beq x18, x19, test82
    c.addi x15, 0x1
test82:
    li x20, 0x03cd73c5
    li x21, 0xd9bccd6f
    p.mulhhuRN x18, x20, x21, 6
    li x19, 0x000cee3e
    beq x18, x19, test83
    c.addi x15, 0x1
test83:
    li x20, 0xf8843486
    li x21, 0xfcfff40d
    p.mulhhuRN x18, x20, x21, 0xa
    li x19, 0x003d665f
    beq x18, x19, test84
    c.addi x15, 0x1
test84:
    li x20, 0x7c03056e
    li x21, 0x70c49147
    p.mulhhuRN x18, x20, x21, 0x17
    li x19, 0x0000006d
    beq x18, x19, test85
    c.addi x15, 0x1
#tests85-90 test the p.macsN instruction. values loaded in and compared to are expected output values
#p.macsN instruction is of format "p.macsN rD, rs1, rs2, ls3". rD[31:0] = (Sext(rs1[15:0]) * Sext(rs2[31:15]) + rD) >>> ls3
test85:
    li x18, 0x6a2e7c11
    li x20, 0x57a8ce44
    li x21, 0x7c6896e9
    p.macsN x18, x20, x21, 0xd
    li x19, 0x0003f4c8
    beq x18, x19, test86
    c.addi x15, 0x1
test86:
    li x18, 0x6413f818
    li x20, 0x6c6fb460
    li x21, 0x4918213a
    p.macsN x18, x20, x21, 2
    li x19, 0x1690cd76
    beq x18, x19, test87
    c.addi x15, 0x1
test87:
    li x18, 0x16f6a68c
    li x20, 0x1b0dc262
    li x21, 0xc21daa61
    p.macsN x18, x20, x21, 7
    li x19, 0x005724c3
    beq x18, x19, test88
    c.addi x15, 0x1
test88:
    li x18, 0x2e606155
    li x20, 0xc269d7ad
    li x21, 0x9046caf0
    p.macsN x18, x20, x21, 0x1b
    li x19, 0x00000006
    beq x18, x19, test89
    c.addi x15, 0x1
test89:
    li x18, 0x75d70d74
    li x20, 0xc7d93cc7
    li x21, 0x7425161d
    p.macsN x18, x20, x21, 0x13
    li x19, 0x00000f62
    beq x18, x19, test90
    c.addi x15, 0x1
test90:
    li x18, 0x2bc1092f
    li x20, 0x6f43d7f1
    li x21, 0xce26920a
    p.macsN x18, x20, x21, 0xa
    li x19, 0x000f3d7a
    beq x18, x19, test91
    c.addi x15, 0x1
#tests91-96 test the p.machhsN instruction. values loaded in and compared to are expected output values
#p.machhsN instruction is of format "p.machhsN rD, rs1, rs2, ls3". rD[31:0] = (Sext(rs1[31:15]) * Sext(rs2[31:15]) + rD) >>> ls3
test91:
    li x18, 0x40fdf1f1
    li x20, 0x71864767
    li x21, 0xdf9f65be
    p.machhsN x18, x20, x21, 9
    li x19, 0x00195117
    beq x18, x19, test92
    c.addi x15, 0x1
test92:
    li x18, 0xa6741035
    li x20, 0x84d3d280
    li x21, 0x243498ec
    p.machhsN x18, x20, x21, 0xf
    li x19, 0xffff2a11
    beq x18, x19, test93
    c.addi x15, 0x1
test93:
    li x18, 0x7833984e
    li x20, 0x49838219
    li x21, 0x9e7cf7d9
    p.machhsN x18, x20, x21, 6
    li x19, 0x0170cc37
    beq x18, x19, test94
    c.addi x15, 0x1
test94:
    li x18, 0x69ce694b
    li x20, 0xc9d1b683
    li x21, 0xb60c38de
    p.machhsN x18, x20, x21, 0xa
    li x19, 0x001e5d5d
    beq x18, x19, test95
    c.addi x15, 0x1
test95:
    li x18, 0x209ff130
    li x20, 0xb780d34f
    li x21, 0x0c0ba5f7
    p.machhsN x18, x20, x21, 2
    li x19, 0x074db4ec
    beq x18, x19, test96
    c.addi x15, 0x1
test96:
    li x18, 0xc0a6df19
    li x20, 0xd8156015
    li x21, 0xb8f77a85
    p.machhsN x18, x20, x21, 0x16
    li x19, 0xffffff2e
    beq x18, x19, test97
    c.addi x15, 0x1
#tests97-102 test the p.macsRN instruction. values loaded in and compared to are expected output values
#p.macsRN instruction is of format "p.macsRN rD, rs1, rs2, ls3". rD[31:0] = (Sext(rs1[15:0]) * Sext(rs2[15:0]) + rD + 2^(ls3-1)) >>> ls3
test97:
    li x18, 0xb1d75295
    li x20, 0xb7ff187f
    li x21, 0xb3b76d7c
    p.macsRN x18, x20, x21, 0xd
    li x19, 0xfffde28a
    beq x18, x19, test98
    c.addi x15, 0x1
test98:
    li x18, 0x6c85dd0d
    li x20, 0x1aaf3098
    li x21, 0xe0749583
    p.macsRN x18, x20, x21, 7
    li x19, 0x0b09e66
    beq x18, x19, test99
    c.addi x15, 0x1
test99:
    li x18, 0x829e3220
    li x20, 0xd6ae528b
    li x21, 0x6be9b0f7
    p.macsRN x18, x20, x21, 1
    li x19, 0x3491331f
    beq x18, x19, test100
    c.addi x15, 0x1
test100:
    li x18, 0x82ba9f8f
    li x20, 0xc1da8695
    li x21, 0x92fa7744
    p.macsRN x18, x20, x21, 0x12
    li x19, 0x0000128a
    beq x18, x19, test101
    c.addi x15, 0x1
test101:
    li x18, 0x15f43032
    li x20, 0x853095fa
    li x21, 0x289272cd
    p.macsRN x18, x20, x21, 0xb
    li x19, 0xfffccd14
    beq x18, x19, test102
    c.addi x15, 0x1
test102:
    li x18, 0x807ce4a5
    li x20, 0x75feee4d
    li x21, 0x62b00035
    p.macsRN x18, x20, x21, 0x15
    li x19, 0xfffffc04
    beq x18, x19, test103
    c.addi x15, 0x1
#tests103-108 test the p.machhsRN instruction. values loaded in and compared to are expected output values
#p.machhsRN instruction is of format "p.machhsRN rD, rs1, rs2, ls3". rD[31:0] = (Sext(rs1[31:15]) * Sext(rs2[31:15]) + rD + 2^(ls3-1)) >>> ls3
test103:
    li x18, 0x40fd6367
    li x20, 0x1621d778
    li x21, 0x4698c081
    p.machhsRN x18, x20, x21, 0xf
    li x19, 0x00008e2f
    beq x18, x19, test104
    c.addi x15, 0x1
test104:
    li x18, 0x026766d0
    li x20, 0xeef80b37
    li x21, 0xd20c6da4
    p.machhsRN x18, x20, x21, 6
    li x19, 0x0015d82a
    beq x18, x19, test105
    c.addi x15, 0x1
test105:
    li x18, 0x809ae8b3
    li x20, 0xa84ec8c1
    li x21, 0x8d14df0f
    p.machhsRN x18, x20, x21, 2
    li x19, 0xe9fe4133
    beq x18, x19, test106
    c.addi x15, 0x1
test106:
    li x18, 0xb00ae2f3
    li x20, 0x4bcdd061
    li x21, 0x8a482256
    p.machhsRN x18, x20, x21, 0x12
    li x19, 0xffffe34c
    beq x18, x19, test107
    c.addi x15, 0x1
test107:
    li x18, 0xe6238423
    li x20, 0xccd49e71
    li x21, 0x4f146a7f
    p.machhsRN x18, x20, x21, 0x19
    li x19, 0xffffffeb
    beq x18, x19, test108
    c.addi x15, 0x1
test108:
    li x18, 0x077d9219
    li x20, 0xfa8f4efa
    li x21, 0x1b8ecf5b
    p.machhsRN x18, x20, x21, 9
    li x19, 0x000373d1
    beq x18, x19, test109
    c.addi x15, 0x1
#tests109-114 test the p.macuN instruction. values loaded in and compared to are expected output values
#p.macuN instruction is of format "p.macuN rD, rs1, rs2, ls3". rD[31:0] = (Zext(rs1[15:0]) * Zext(rs2[31:15]) + rD) >> ls3
test109:
    li x18, 0x5bca07fb
    li x20, 0xbcc46afd
    li x21, 0xd8721ad7
    p.macuN x18, x20, x21, 8
    li x19, 0x670194
    beq x18, x19, test110
    c.addi x15, 0x1
test110:
    li x18, 0x9c521928
    li x20, 0x82f89100
    li x21, 0x72103b7a
    p.macuN x18, x20, x21, 0xc
    li x19, 0x000be023
    beq x18, x19, test111
    c.addi x15, 0x1
test111:
    li x18, 0x01d5fc7d
    li x20, 0xb0c40752
    li x21, 0x38952318
    p.macuN x18, x20, x21, 5
    li x19, 0x0016b711
    beq x18, x19, test112
    c.addi x15, 0x1
test112:
    li x18, 0x0cb435b5
    li x20, 0x2575c2ee
    li x21, 0xc8836a0e
    p.macuN x18, x20, x21, 0x12
    li x19, 0x0000175d
    beq x18, x19, test113
    c.addi x15, 0x1
test113:
    li x18, 0x8d593849
    li x20, 0x0cd78dc2
    li x21, 0x688d2e0b
    p.macuN x18, x20, x21, 3 
    li x19, 0x14db0573
    beq x18, x19, test114
    c.addi x15, 0x1
test114:
    li x18, 0x8659af2c
    li x20, 0xb756fd2b
    li x21, 0xd4ce16ee
    p.macuN x18, x20, x21, 0x17
    li x19, 0x0000013a
    beq x18, x19, test115
    c.addi x15, 0x1
#tests115-120 test the p.machhuN instruction. values loaded in and compared to are expected output values
#p.machhuN instruction is of format "p.machhuN rD, rs1, rs2, ls3". rD[31:0] = (Zext(rs1[31:15]) * Zext(rs2[31:15]) + rD) >> ls3
test115:
    li x18, 0x715ef760
    li x20, 0xa215e735
    li x21, 0x02a34d70
    p.machhuN x18, x20, x21, 0xe
    li x19, 0x0001cc29
    beq x18, x19, test116
    c.addi x15, 0x1
test116:
    li x18, 0xebeeede1
    li x20, 0x7363e8cb
    li x21, 0xdbaecfe0
    p.machhuN x18, x20, x21, 2
    li x19, 0x13bcc30a
    beq x18, x19, test117
    c.addi x15, 0x1
test117:
    li x18, 0xcee2e5b0
    li x20, 0x99e14ec0
    li x21, 0xc1e4b273
    p.machhuN x18, x20, x21, 7
    li x19, 0x0086dd26
    beq x18, x19, test118
    c.addi x15, 0x1
test118:
    li x18, 0x211da244
    li x20, 0xdb749b50
    li x21, 0xcc7af2da
    p.machhuN x18, x20, x21, 0xa
    li x19, 0x003419a9
    beq x18, x19, test119
    c.addi x15, 0x1
test119:
    li x18, 0x95b52cc7
    li x20, 0xb9be6816
    li x21, 0xeaf964be
    p.machhuN x18, x20, x21, 0x15
    li x19, 0x00000201
    beq x18, x19, test120
    c.addi x15, 0x1
test120:
    li x18, 0xcfc106bd
    li x20, 0xade1a537
    li x21, 0x7d456dfb
    p.machhuN x18, x20, x21, 5
    li x19, 0x0126b60b
    beq x18, x19, test121
    c.addi x15, 0x1
#tests121-126 test the p.macuRN instruction. values loaded in and compared to are expected output values
#p.macuRN instruction is of format "p.macuRN rD, rs1, rs2, ls3". rD[31:0] = (Zext(rs1[15:0]) * Zext(rs2[15:0]) + rD + 2^(ls3-1)) >> ls3
test121:
    li x18, 0x400a5e9a
    li x20, 0xd6dbd128
    li x21, 0xe5a1a96f
    p.macuRN x18, x20, x21, 0xb
    li x19, 0x00194f0f
    beq x18, x19, test122
    c.addi x15, 0x1
test122:
    li x18, 0x6371836d
    li x20, 0xbc604581
    li x21, 0x445aeea5
    p.macuRN x18, x20, x21, 8
    li x19, 0x00a43c3e
    beq x18, x19, test123
    c.addi x15, 0x1
test123:
    li x18, 0x469879de
    li x20, 0x08a5ad4d
    li x21, 0x642d7edf
    p.macuRN x18, x20, x21, 3
    li x19, 0x138f6abe
    beq x18, x19, test124
    c.addi x15, 0x1
test124:
    li x18, 0xea104bc3
    li x20, 0xd92e39cc
    li x21, 0x6474e421
    p.macuRN x18, x20, x21, 0x15
    li x19, 0x000000ed
    beq x18, x19, test125
    c.addi x15, 0x1
test125:
    li x18, 0xe765e24e
    li x20, 0x4e17470b
    li x21, 0xc55e9600
    p.macuRN x18, x20, x21, 0xd
    li x19, 0x00008833
    beq x18, x19, test126
    c.addi x15, 0x1
test126:
    li x18, 0x3def16e1
    li x20, 0x4b5a1d37
    li x21, 0xb4c52043
    p.macuRN x18, x20, x21, 0x11
    li x19, 0x000020cf
    beq x18, x19, test127
    c.addi x15, 0x1
#tests127-132 test the p.machhuRN instruction. values loaded in and compared to are expected output values
#p.machhuRN instruction is of format "p.machhuRN rD, rs1, rs2, ls3". rD[31:0] = (Zext(rs1[31:15]) * Zext(rs2[31:15]) + rD + 2^(ls3-1)) >> ls3
test127:
    li x18, 0x27dac03d
    li x20, 0xf83d2546
    li x21, 0xd8eb64fd
    p.machhuRN x18, x20, x21, 3
    li x19, 0x1f464308
    beq x18, x19, test128
    c.addi x15, 0x1
test128:
    li x18, 0xca3923cc
    li x20, 0x3bad5492
    li x21, 0x22b9c984
    p.machhuRN x18, x20, x21, 0x1f
    li x19, 0x00000000
    beq x18, x19, test129
    c.addi x15, 0x1
test129:
    li x18, 0xb5dd5975
    li x20, 0x0b497b58
    li x21, 0xc98b5324
    p.machhuRN x18, x20, x21, 0xd
    li x19, 0x0005f5fe
    beq x18, x19, test130
    c.addi x15, 0x1
test130:
    li x18, 0x01e2fe68
    li x20, 0x4881f1b4
    li x21, 0xf242cebf
    p.machhuRN x18, x20, x21, 0x5
    li x19, 0x0233fd0d
    beq x18, x19, test131
    c.addi x15, 0x1
test131:
    li x18, 0x7ff4ce78
    li x20, 0x6e91ac4b
    li x21, 0xf7b7766f
    p.machhuRN x18, x20, x21, 0x11
    li x19, 0x00007579
    beq x18, x19, test132
    c.addi x15, 0x1
test132:
    li x18, 0x5fad7f7e
    li x20, 0x35c8b6c1
    li x21, 0x3ff4ab69
    p.machhuRN x18, x20, x21, 0x16
    li x19, 0x000001b4
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
