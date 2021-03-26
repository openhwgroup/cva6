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
#tests1-6 test the pv.shuffle.h instruction. values loaded in and compared to are expected output values
#pv.shuffle.h is of the form "pv.shuffle.h rD, rs1, rs2".
test1:
    li x17, 0xeb3d8bec
    li x18, 0xdd2cd85f
    pv.shuffle.h x19, x17, x18
    li x20, 0x8beceb3d
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x98c7e168
    li x18, 0xad2df825
    pv.shuffle.h x19, x17, x18
    li x20, 0x98c798c7
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0x8c1ad07e
    li x18, 0xbf62d942
    pv.shuffle.h x19, x17, x18
    li x20, 0xd07ed07e
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x2f661389
    li x18, 0xdd07991d
    pv.shuffle.h x19, x17, x18
    li x20, 0x2f662f66
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0x1934aee5
    li x18, 0x82ef3f3a
    pv.shuffle.h x19, x17, x18
    li x20, 0x1934aee5
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x54580572
    li x18, 0x3c6e07f4
    pv.shuffle.h x19, x17, x18
    li x20, 0x05720572
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.shuffle.sci.h instruction. values loaded in and compared to are expected output values
#pv.shuffle.sci.h is of the form "pv.shuffle.sci.h rD, rs1, Imm6".
test7:
    li x17, 0x65611a7f
    pv.shuffle.sci.h x19, x17, 0xb
    li x20, 0x65616561
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0xb03ec1e9
    pv.shuffle.sci.h x19, x17, 0x5
    li x20, 0xc1e9b03e
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x656b1acf
    pv.shuffle.sci.h x19, x17, 0x7
    li x20, 0x656b656b
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0xc8440911
    pv.shuffle.sci.h x19, x17, 0xc
    li x20, 0x09110911
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0xaf077cef
    pv.shuffle.sci.h x19, x17, 0xe
    li x20, 0xaf077cef
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x374e3a34
    pv.shuffle.sci.h x19, x17, 0x1
    li x20, 0x3a34374e
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.shuffle.b instruction. values loaded in and compared to are expected output values
#pv.shuffle.b is of the form "pv.shuffle.b rD, rs1, rs2".
test13:
    li x17, 0x442e57db
    li x18, 0x847478f0
    pv.shuffle.b x19, x17, x18
    li x20, 0xdbdbdbdb
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0x6d0febb3
    li x18, 0x5c9476e3
    pv.shuffle.b x19, x17, x18
    li x20, 0xb3b30f6d
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0x2afa56b0
    li x18, 0x9e5657fd
    pv.shuffle.b x19, x17, x18
    li x20, 0xfafa2a56
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0x0cf589bc
    li x18, 0xbe2bc2b8
    pv.shuffle.b x19, x17, x18
    li x20, 0xf50cf5bc
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x36347756
    li x18, 0x4e66d17a
    pv.shuffle.b x19, x17, x18
    li x20, 0x34347734
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0xe3a6da52
    li x18, 0x135c2125
    pv.shuffle.b x19, x17, x18
    li x20, 0xe352dada
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.shuffleI0.sci.b instruction. values loaded in and compared to are expected output values
#pv.shuffleI0.sci.b is of the form "pv.shuffleI0.sci.b rD, rs1, Imm6".
test19:
    li x17, 0x46caee88
    pv.shuffleI0.sci.b x19, x17, 50
    li x20, 0x884688ca
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x958f6050
    pv.shuffleI0.sci.b x19, x17, 12
    li x20, 0x50509550
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0xf03ee7d0
    pv.shuffleI0.sci.b x19, x17, 2
    li x20, 0xd0d0d03e
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0xaeaa31e2
    pv.shuffleI0.sci.b x19, x17, 46
    li x20, 0xe2aaaeaa
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0x8271df42
    pv.shuffleI0.sci.b x19, x17, 34
    li x20, 0x42714271
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0x8f7084d6
    pv.shuffleI0.sci.b x19, x17, 22
    li x20, 0xd6848470
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.shuffleI1.sci.b instruction. values loaded in and compared to are expected output values
#pv.shuffleI1.sci.b is of the form "pv.shuffleI1.sci.b rD, rs1, Imm6".
test25:
    li x17, 0x817e3e19
    pv.shuffleI1.sci.b x19, x17, 16
    li x20, 0x3e3e1919
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0xb5a8378f
    pv.shuffleI1.sci.b x19, x17, 46
    li x20, 0x37a8b5a8
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0x039d72d9
    pv.shuffleI1.sci.b x19, x17, 28
    li x20, 0x727203d9
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0x120c3083
    pv.shuffleI1.sci.b x19, x17, 3
    li x20, 0x30838312
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0x734e8f95
    pv.shuffleI1.sci.b x19, x17, 13
    li x20, 0x8f95738f
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0x63782b7f
    pv.shuffleI1.sci.b x19, x17, 31
    li x20, 0x2b2b6363
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.shuffleI2.sci.b instruction. values loaded in and compared to are expected output values
#pv.shuffleI2.sci.b is of the form "pv.shuffleI2.sci.b rD, rs1, Imm6".
test31:
    li x17, 0xac800f82
    pv.shuffleI2.sci.b x19, x17, 41
    li x20, 0x8080800f
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0xe5f83eef
    pv.shuffleI2.sci.b x19, x17, 18
    li x20, 0xf83eeff8
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0xcf04e07a
    pv.shuffleI2.sci.b x19, x17, 32
    li x20, 0x04047a7a
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0xde8e49ec
    pv.shuffleI2.sci.b x19, x17, 5
    li x20, 0x8eec4949
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x01a6fcfb
    pv.shuffleI2.sci.b x19, x17, 37
    li x20, 0xa6a6fcfc
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0xa8092856
    pv.shuffleI2.sci.b x19, x17, 4
    li x20, 0x09562856
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.shuffleI3.sci.b instruction. values loaded in and compared to are expected output values
#pv.shuffleI3.sci.b is of the form "pv.shuffleI3.sci.b rD, rs1, Imm6".
test37:
    li x17, 0x1e53472c
    pv.shuffleI3.sci.b x19, x17, 14
    li x20, 0x1e2c1e53
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0x8b09bdff
    pv.shuffleI3.sci.b x19, x17, 53
    li x20, 0x8b8bbdbd
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0x2300a758
    pv.shuffleI3.sci.b x19, x17, 26
    li x20, 0x23a70000
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x6c6b9079
    pv.shuffleI3.sci.b x19, x17, 37
    li x20, 0x6c6b9090
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0x51d0126b
    pv.shuffleI3.sci.b x19, x17, 19
    li x20, 0x51126b51
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0x52dc2310
    pv.shuffleI3.sci.b x19, x17, 34
    li x20, 0x52dc10dc
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.shuffle2.h instruction. values loaded in and compared to are expected output values
#pv.shuffle2.h is of the form "pv.shuffle2.h rD, rs1, rs2".
test43:
    li x19, 0x0b83e7f5
    li x17, 0xb4af2179
    li x18, 0x8b3540e7
    pv.shuffle2.h x19, x17, x18
    li x20, 0x0b83b4af
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x19, 0x51d53e8b
    li x17, 0xcb38f5fa
    li x18, 0xa81a2f04
    pv.shuffle2.h x19, x17, x18
    li x20, 0xf5fa3e8b
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x19, 0xf8ef994a
    li x17, 0xd3bc7138
    li x18, 0x28d1d162
    pv.shuffle2.h x19, x17, x18
    li x20, 0xf8ef7138
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x19, 0xbf137992
    li x17, 0x3b91dc38
    li x18, 0x6af5562d
    pv.shuffle2.h x19, x17, x18
    li x20, 0xbf13bf13
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x19, 0x0efea2f4
    li x17, 0x3123bc4b
    li x18, 0xc62ec5c8
    pv.shuffle2.h x19, x17, x18
    li x20, 0xbc4ba2f4
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x19, 0x9601ba9d
    li x17, 0x2e6cbc1c
    li x18, 0xd94c2e91
    pv.shuffle2.h x19, x17, x18
    li x20, 0xba9d9601
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.shuffle2.b instruction. values loaded in and compared to are expected output values
#pv.shuffle2.b is of the form "pv.shuffle2.b rD, rs1, rs2".
test49:
    li x19, 0x9d7c9732
    li x17, 0x2e088505
    li x18, 0x31a1f55b
    pv.shuffle2.b x19, x17, x18
    li x20, 0x9797859d
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x19, 0x425401e8
    li x17, 0x6ca51c69
    li x18, 0x98733f07
    pv.shuffle2.b x19, x17, x18
    li x20, 0xe8426c6c
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x19, 0x5e2f2887
    li x17, 0x6c397eb0
    li x18, 0x09f51ade
    pv.shuffle2.b x19, x17, x18
    li x20, 0x287e2f39
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x19, 0xe24c00ae
    li x17, 0x7f0c37fe
    li x18, 0xfd4d2913
    pv.shuffle2.b x19, x17, x18
    li x20, 0x373700e2
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x19, 0x873cf3a7
    li x17, 0x6941a151
    li x18, 0x34e3e584
    pv.shuffle2.b x19, x17, x18
    li x20, 0x5187a151
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x19, 0xab6e9899
    li x17, 0x91ac6945
    li x18, 0x4fe339fe
    pv.shuffle2.b x19, x17, x18
    li x20, 0x91ab98ac
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.pack instruction. values loaded in and compared to are expected output values
#pv.pack is of the form "pv.pack rD, rs1, rs2".
test55:
    li x17, 0xe9ee2e5f
    li x18, 0xad8637dc
    .word(0xd12889d7)    #pv.pack x19, x17, x18
    li x20, 0x2e5f37dc
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0xafcc2cde
    li x18, 0x7851d370
    .word(0xd12889d7)    #pv.pack x19, x17, x18
    li x20, 0x2cded370
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0xd7686bd6
    li x18, 0x06b0edf1
    .word(0xd12889d7)    #pv.pack x19, x17, x18
    li x20, 0x6bd6edf1
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0x5d71c849
    li x18, 0x0bad7dbc
    .word(0xd12889d7)    #pv.pack x19, x17, x18
    li x20, 0xc8497dbc
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0xc997af18
    li x18, 0x7a5eb90a
    .word(0xd12889d7)    #pv.pack x19, x17, x18
    li x20, 0xaf18b90a
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0x80689e7c
    li x18, 0x795874bc
    .word(0xd12889d7)    #pv.pack x19, x17, x18
    li x20, 0x9e7c74bc
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.pack.h instruction. values loaded in and compared to are expected output values
#pv.pack.h is of the form "pv.pack.h rD, rs1, rs2".
test61:
    li x17, 0xffc16020
    li x18, 0x35374e9a
    .word(0xd32889d7)    #pv.pack.h x19, x17, x18
    li x20, 0xffc13537
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x932ecc38
    li x18, 0x1ae6c08b
    .word(0xd32889d7)    #pv.pack.h x19, x17, x18
    li x20, 0x932e1ae6
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0x14c1d05f
    li x18, 0x59a6e2e8
    .word(0xd32889d7)    #pv.pack.h x19, x17, x18
    li x20, 0x14c159a6
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0xceed5661
    li x18, 0xb66ae4c4
    .word(0xd32889d7)    #pv.pack.h x19, x17, x18
    li x20, 0xceedb66a
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0x8ddc12c1
    li x18, 0x7b15b740
    .word(0xd32889d7)    #pv.pack.h x19, x17, x18
    li x20, 0x8ddc7b15
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0x61c756e4
    li x18, 0x74e224e9
    .word(0xd32889d7)    #pv.pack.h x19, x17, x18
    li x20, 0x61c774e2
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.packhi.b instruction. values loaded in and compared to are expected output values
#pv.packhi.b is of the form "pv.packhi.b rD, rs1, rs2".
test67:
    li x19, 0xbe89360e
    li x17, 0xb2a0cdb8
    li x18, 0x69296b12
    pv.packhi.b x19, x17, x18
    li x20, 0xb812360e
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x19, 0x43fbb89c
    li x17, 0x7a5dc8fd
    li x18, 0x95c4c385
    pv.packhi.b x19, x17, x18
    li x20, 0xfd85b89c
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x19, 0x44ce42c2
    li x17, 0x9fe7387b
    li x18, 0x7cec73c2
    pv.packhi.b x19, x17, x18
    li x20, 0x7bc242c2
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x19, 0x8d6f2721
    li x17, 0x3b68bac0
    li x18, 0x18ccf3ea
    pv.packhi.b x19, x17, x18
    li x20, 0xc0ea2721
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x19, 0x46ab14fa
    li x17, 0x4c6abd63
    li x18, 0xd790a6fe
    pv.packhi.b x19, x17, x18
    li x20, 0x63fe14fa
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x19, 0x5c40f45b
    li x17, 0x29b0f7e5
    li x18, 0x061253a0
    pv.packhi.b x19, x17, x18
    li x20, 0xe5a0f45b
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.packlo.b instruction. values loaded in and compared to are expected output values
#pv.packlo.b is of the form "pv.packlo.b rD, rs1, rs2".
test73:
    li x19, 0xa12f98e7
    li x17, 0x15fb2adb
    li x18, 0x1bca2b4c
    pv.packlo.b x19, x17, x18
    li x20, 0xa12fdb4c
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x19, 0xe1401313
    li x17, 0x01bec6dd
    li x18, 0x3f9f4a72
    pv.packlo.b x19, x17, x18
    li x20, 0xe140dd72
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x19, 0xe572684c
    li x17, 0x6433a202
    li x18, 0x296e2d47
    pv.packlo.b x19, x17, x18
    li x20, 0xe5720247
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x19, 0x2fd584b4
    li x17, 0x9909ae84
    li x18, 0x76d02d46
    pv.packlo.b x19, x17, x18
    li x20, 0x2fd58446
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x19, 0x6875cc28
    li x17, 0x5a2a5938
    li x18, 0x3ce2177c
    pv.packlo.b x19, x17, x18
    li x20, 0x6875387c
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x19, 0xdd50e6c1
    li x17, 0x1ba9d08d
    li x18, 0x5f2a0e4b
    pv.packlo.b x19, x17, x18
    li x20, 0xdd508d4b
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
