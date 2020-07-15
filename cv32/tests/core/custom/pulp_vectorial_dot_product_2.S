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
#tests1-6 test the pv.sdotup.h instruction. values loaded in and compared to are expected output values
#pv.sdotup.h is of the form "pv.sdotup.h rD, rs1, rs2"
test1:
    li x19, 0xa02c2a67
    li x17, 0x8d7fd0d4
    li x18, 0xfc7b09b2
    pv.sdotup.h x19, x17, x18
    li x20, 0x33a1d1d4
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x19, 0xe203b60c
    li x17, 0x30794165
    li x18, 0x746b2820
    pv.sdotup.h x19, x17, x18
    li x20, 0x024ec13f
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x19, 0x73a09426
    li x17, 0xd3b7e82c
    li x18, 0x095ccaf7
    pv.sdotup.h x19, x17, x18
    li x20, 0x3370d35e
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x19, 0x2fa589c2
    li x17, 0x8147d144
    li x18, 0x6f633d3a
    pv.sdotup.h x19, x17, x18
    li x20, 0x99f1ee9f
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x19, 0xe713a432
    li x17, 0xd264baa9
    li x18, 0x40f0b913
    pv.sdotup.h x19, x17, x18
    li x20, 0xa363dd7d
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x19, 0xc676189d
    li x17, 0x9e2d2f27
    li x18, 0xa14bf1a7
    pv.sdotup.h x19, x17, x18
    li x20, 0x56a1363d
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.sdotup.sc.h instruction. values loaded in and compared to are expected output values
#pv.sdotup.sc.h is of the form "pv.sdotup.sc.h rD, rs1, rs2"
test7:
    li x19, 0x1b197fca
    li x17, 0x7850ff4b
    li x18, 0xf74314d0
    pv.sdotup.sc.h x19, x17, x18
    li x20, 0x39a2c9ba
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x19, 0xa2a2c0ee
    li x17, 0xeed2cf26
    li x18, 0x4e449958
    pv.sdotup.sc.h x19, x17, x18
    li x20, 0xadc5462e
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x19, 0xe4f67358
    li x17, 0x99c5cb0c
    li x18, 0x602feda7
    pv.sdotup.sc.h x19, x17, x18
    li x20, 0x3034b4af
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x19, 0xec17ce6e
    li x17, 0x76f60132
    li x18, 0xfb3365f7
    pv.sdotup.sc.h x19, x17, x18
    li x20, 0x1bf38506
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x19, 0xdf3cee3a
    li x17, 0x9f2bae05
    li x18, 0xe194c218
    pv.sdotup.sc.h x19, x17, x18
    li x20, 0xdbda8aba
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x19, 0xa6839365
    li x17, 0xa1e360b5
    li x18, 0xbd1db2ec
    pv.sdotup.sc.h x19, x17, x18
    li x20, 0x5b3fa785
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.sdotup.sci.h instruction. values loaded in and compared to are expected output values
#pv.sdotup.sci.h is of the form "pv.sdotup.sci.h rD, rs1, Imm6"
test13:
    li x19, 0x545fff15
    li x17, 0xc30a2b68
    pv.sdotup.sci.h x19, x17, 0x1f
    li x20, 0x547cdee3
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x19, 0xf65ec051
    li x17, 0x96437fa8
    pv.sdotup.sci.h x19, x17, 0x04
    li x20, 0xf66317fd
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x19, 0x455a3d6f
    li x17, 0x0eba82f5
    pv.sdotup.sci.h x19, x17, 0x1d
    li x20, 0x456abe42
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x19, 0xbdb2196a
    li x17, 0xf8069c7d
    pv.sdotup.sci.h x19, x17, 0x08
    li x20, 0xbdbebd82
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x19, 0xc81e285e
    li x17, 0x8dff2c6d
    pv.sdotup.sci.h x19, x17, 0x0b
    li x20, 0xc8262b02
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x19, 0x02ac2919
    li x17, 0x70ea0687
    pv.sdotup.sci.h x19, x17, 0x15
    li x20, 0x02b5f55e
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.sdotup.b instruction. values loaded in and compared to are expected output values
#pv.sdotup.b is of the form "pv.sdotup.b rD, rs1, rs2"
test19:
    li x19, 0x12ef7631
    li x17, 0xc71e0ac8
    li x18, 0x04ae1745
    pv.sdotup.b x19, x17, x18
    li x20, 0x12efc47f
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x19, 0x7c5ec5c9
    li x17, 0x155abaf5
    li x18, 0x13fe66b2
    pv.sdotup.b x19, x17, x18
    li x20, 0x7c60151a
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x19, 0x2b9998e3
    li x17, 0x9d63534a
    li x18, 0xcde8e371
    pv.sdotup.b x19, x17, x18
    li x20, 0x2b9ada97
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x19, 0x289b0378
    li x17, 0x508b2b5d
    li x18, 0x51f8078f
    pv.sdotup.b x19, x17, x18
    li x20, 0x289bd890
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x19, 0x836f94ce
    li x17, 0x0777091d
    li x18, 0xa1ac9cf4
    pv.sdotup.b x19, x17, x18
    li x20, 0x83700a49
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x19, 0xfe85aa49
    li x17, 0xadc46b3f
    li x18, 0x50cadfb3
    pv.sdotup.b x19, x17, x18
    li x20, 0xfe870443
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.sdotup.sc.b instruction. values loaded in and compared to are expected output values
#pv.or.sc.b is of the form "pv.sdotup.sc.b rD, rs1, rs2"
test25:
    li x19, 0x716c4d86
    li x17, 0x723a555c
    li x18, 0xc58efe52
    pv.sdotup.sc.b x19, x17, x18
    li x20, 0x716cbd50
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x19, 0xe2442067
    li x17, 0xad02556e
    li x18, 0xb8cce704
    pv.sdotup.sc.b x19, x17, x18
    li x20, 0xe244262f
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x19, 0x5a8e7cc2
    li x17, 0x25b8d3e3
    li x18, 0x6cf178db
    pv.sdotup.sc.b x19, x17, x18
    li x20, 0x5a90b083
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x19, 0xa6b443ee
    li x17, 0xdab28669
    li x18, 0x3ec976e3
    pv.sdotup.sc.b x19, x17, x18
    li x20, 0xa6b676ff
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x19, 0x2fc3f0b9
    li x17, 0xb8f9ec8f
    li x18, 0x50ca6bb5
    pv.sdotup.sc.b x19, x17, x18
    li x20, 0x2fc62ed5
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x19, 0xe4763281
    li x17, 0xbe578060
    li x18, 0x0b332fdd
    pv.sdotup.sc.b x19, x17, x18
    li x20, 0xe477e302
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.sdotup.sci.b instruction. values loaded in and compared to are expected output values
#pv.sdotup.sci.b is of the form "pv.sdotup.sci.b rD, rs1, Imm6"
test31:
    li x19, 0x162fbd9a
    li x17, 0x375cf3e1
    pv.sdotup.sci.b x19, x17, 0x0a
    li x20, 0x162fd5a0
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x19, 0x46cee932
    li x17, 0x741ff4fd
    pv.sdotup.sci.b x19, x17, 0x02
    li x20, 0x46ceee3a
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x19, 0x66ffbaf5
    li x17, 0x64379371
    pv.sdotup.sci.b x19, x17, 0x1c
    li x20, 0x66ffe859
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x19, 0x9220ebce
    li x17, 0x70095e27
    pv.sdotup.sci.b x19, x17, 0x04
    li x20, 0x9220efc6
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x19, 0x29e4b1bf
    li x17, 0xed23b04c
    pv.sdotup.sci.b x19, x17, 0x08
    li x20, 0x29e4c21f
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x19, 0x481efa13
    li x17, 0xb73e73df
    pv.sdotup.sci.b x19, x17, 0x0e
    li x20, 0x481f19f5
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.sdotusp.h instruction. values loaded in and compared to are expected output values
#pv.sdotusp.h is of the form "pv.sdotusp.h rD, rs1, rs2"
test37:
    li x19, 0x10b8147a
    li x17, 0xc2b4bab2
    li x18, 0x28efdc3e
    pv.sdotusp.h x19, x17, x18
    li x20, 0x15c629a2
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x19, 0xb9f31792
    li x17, 0x361d7b9d
    li x18, 0xf44d555f
    pv.sdotusp.h x19, x17, x18
    li x20, 0xe0b3028e
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x19, 0x495ffc6b
    li x17, 0x8bcd51a1
    li x18, 0xe6af416e
    pv.sdotusp.h x19, x17, x18
    li x20, 0x5069afbc
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x19, 0x38bf90b1
    li x17, 0x10ca59e2
    li x18, 0x3d1144be
    pv.sdotusp.h x19, x17, x18
    li x20, 0x54e38dd7
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x19, 0xb9a73cef
    li x17, 0xbc490bca
    li x18, 0xb659cf99
    pv.sdotusp.h x19, x17, x18
    li x20, 0x8140fa0a
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x19, 0xcd913e6e
    li x17, 0xda832e89
    li x18, 0xa406e8ce
    pv.sdotusp.h x19, x17, x18
    li x20, 0x7ad7e3be
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.sdotusp.sc.h instruction. values loaded in and compared to are expected output values
#pv.sdotusp.sc.h is of the form "pv.sdotusp.sc.h rD, rs1, rs2"
test43:
    li x19, 0xa4fac58c
    li x17, 0x75d8c786
    li x18, 0x073d4040
    pv.sdotusp.sc.h x19, x17, x18
    li x20, 0xf4a19d0c
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x19, 0x197172aa
    li x17, 0xc9de6255
    li x18, 0x4a01ff57
    pv.sdotusp.sc.h x19, x17, x18
    li x20, 0x18ab44ff
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x19, 0xc390e5ca
    li x17, 0xc5a6c38b
    li x18, 0xf78a072c
    pv.sdotusp.sc.h x19, x17, x18
    li x20, 0xce94d136
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x19, 0x913d4bd1
    li x17, 0x007bee13
    li x18, 0x3a930631
    pv.sdotusp.sc.h x19, x17, x18
    li x20, 0x970248ff
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x19, 0x9dd4ddd6
    li x17, 0xc18ca673
    li x18, 0x1d4c393f
    pv.sdotusp.sc.h x19, x17, x18
    li x20, 0xee553c97
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x19, 0x0d1ae27d
    li x17, 0xd1931c9c
    li x18, 0xc652343d
    pv.sdotusp.sc.h x19, x17, x18
    li x20, 0x3db52fb0
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.sdotusp.sci.h instruction. values loaded in and compared to are expected output values
#pv.sdotusp.sci.h is of the form "pv.sdotusp.sci.h rD, rs1, Imm6"
test49:
    li x19, 0xa372f233
    li x17, 0x9898f9da
    pv.sdotusp.sci.h x19, x17, 0x0f
    li x20, 0xa38a86e1
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x19, 0xa5bef506
    li x17, 0x3906a14c
    pv.sdotusp.sci.h x19, x17, 0x1f
    li x20, 0xa5d964f4
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x19, 0x22a6fe4f
    li x17, 0x68b23822
    pv.sdotusp.sci.h x19, x17, 0x05
    li x20, 0x22aa2273
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x19, 0x78ae7867
    li x17, 0x3f9fc689
    pv.sdotusp.sci.h x19, x17, 0x14
    li x20, 0x78c2f387
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x19, 0x90e93731
    li x17, 0x2cbd4d4d
    pv.sdotusp.sci.h x19, x17, 0x0d
    li x20, 0x90ef69b3
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x19, 0xc18ec5d2
    li x17, 0x767f1301
    pv.sdotusp.sci.h x19, x17, 0x05
    li x20, 0xc1917552
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.sdotusp.b instruction. values loaded in and compared to are expected output values
#pv.sdotusp.b is of the form "pv.sdotusp.b rD, rs1, rs2"
test55:
    li x19, 0xa6f55edb
    li x17, 0x78b948eb
    li x18, 0xa10db278
    pv.sdotusp.b x19, x17, x18
    li x20, 0xa6f593f0
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x19, 0xa6f7a2c8
    li x17, 0x8a0044d4
    li x18, 0x956ca42c
    pv.sdotusp.b x19, x17, x18
    li x20, 0xa6f7751a
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x19, 0x33f4f487
    li x17, 0x1f438bc2
    li x18, 0xa2878bc4
    pv.sdotusp.b x19, x17, x18
    li x20, 0x33f45c7b
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x19, 0xd4095822
    li x17, 0x441ff178
    li x18, 0x7b692489
    pv.sdotusp.b x19, x17, x18
    li x20, 0xd4096fa1
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x19, 0x095b9429
    li x17, 0xb2283b1a
    li x18, 0x70cf688f
    pv.sdotusp.b x19, x17, x18
    li x20, 0x095be6df
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x19, 0xce188cd0
    li x17, 0x54cfaa4d
    li x18, 0xc917967e
    pv.sdotusp.b x19, x17, x18
    li x20, 0xce186cdf
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.sdotusp.sc.b instruction. values loaded in and compared to are expected output values
#pv.sdotusp.sc.b is of the form "pv.sdotusp.sc.b rD, rs1, rs2"
test61:
    li x19, 0xe148067f
    li x17, 0x3288c6b0
    li x18, 0x0bc36aea
    pv.sdotusp.sc.b x19, x17, x18
    li x20, 0xe147d65f
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x19, 0x3664e60b
    li x17, 0x2cd847f0
    li x18, 0x12d2fdbc
    pv.sdotusp.sc.b x19, x17, x18
    li x20, 0x36644e5f
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x19, 0x6b3163ff
    li x17, 0xfca71bac
    li x18, 0x5fae1422
    pv.sdotusp.sc.b x19, x17, x18
    li x20, 0x6b31b613
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x19, 0x2dcdd299
    li x17, 0x8869ea62
    li x18, 0xafe8b45b
    pv.sdotusp.sc.b x19, x17, x18
    li x20, 0x2dce9e48
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x19, 0x4aaf236b
    li x17, 0x5c517c0b
    li x18, 0xe895d795
    pv.sdotusp.sc.b x19, x17, x18
    li x20, 0x4aaea2af
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x19, 0x76fb9587
    li x17, 0xeb055bef
    li x18, 0xe96cfb9b
    pv.sdotusp.sc.b x19, x17, x18
    li x20, 0x76fab4a5
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.sdotusp.sci.b instruction. values loaded in and compared to are expected output values
#pv.sdotusp.sci.b is of the form "pv.sdotusp.sci.b rD, rs1, Imm6"
test67:
    li x19, 0x50588517
    li x17, 0xa222991a
    pv.sdotusp.sci.b x19, x17, 0x10
    li x20, 0x50589c87
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x19, 0x47c672af
    li x17, 0x7d071124
    pv.sdotusp.sci.b x19, x17, 0x1d
    li x20, 0x47c687a4
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x19, 0x21b018e9
    li x17, 0xcd97df91
    pv.sdotusp.sci.b x19, x17, 0x0c
    li x20, 0x21b03ad9
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x19, 0x145940ed
    li x17, 0x3276e2da
    pv.sdotusp.sci.b x19, x17, 0x0d
    li x20, 0x14596001
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x19, 0x3eb4ebf3
    li x17, 0xa4548d4c
    pv.sdotusp.sci.b x19, x17, 0x07
    li x20, 0x3eb4f8aa
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x19, 0x05d39623
    li x17, 0xde5c08dd
    pv.sdotusp.sci.b x19, x17, 0x06
    li x20, 0x05d3a2dd
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.sdotsp.h instruction. values loaded in and compared to are expected output values
#pv.sdotsp.h is of the form "pv.sdotsp.h rD, rs1, rs2"
test73:
    li x19, 0xc13fcb61
    li x17, 0x32617430
    li x18, 0xf6237fd6
    pv.sdotsp.h x19, x17, x18
    li x20, 0xf953d4c4
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x19, 0x392f2cab
    li x17, 0x45670453
    li x18, 0x1c9fe38c
    pv.sdotsp.h x19, x17, x18
    li x20, 0x40768208
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x19, 0x167c58cc
    li x17, 0x1b9d05f3
    li x18, 0x466033ff
    pv.sdotsp.h x19, x17, x18
    li x20, 0x1f48f7b9
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x19, 0xfbb9b14f
    li x17, 0x62b680f5
    li x18, 0xd035b500
    pv.sdotsp.h x19, x17, x18
    li x20, 0x0e8439fd
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x19, 0xefd58612
    li x17, 0x3950ad4e
    li x18, 0x9f1fd488
    pv.sdotsp.h x19, x17, x18
    li x20, 0xe82fd032
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x19, 0x671b63ed
    li x17, 0xe6f68033
    li x18, 0x08f643ba
    pv.sdotsp.h x19, x17, x18
    li x20, 0x446b825f
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the pv.sdotsp.sc.h instruction. values loaded in and compared to are expected output values
#pv.sdotsp.sc.h is of the form "pv.sdotsp.sc.h rD, rs1, rs2"
test79:
    li x19, 0x5cd3f582
    li x17, 0x5f534237
    li x18, 0xe5f45f7a
    pv.sdotsp.sc.h x19, x17, x18
    li x20, 0x99132746
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x19, 0xaa3caa98
    li x17, 0xcc81894c
    li x18, 0x611b6e10
    pv.sdotsp.sc.h x19, x17, x18
    li x20, 0x61101d68
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x19, 0x5a7ae574
    li x17, 0xe4176d99
    li x18, 0x86264b2a
    pv.sdotsp.sc.h x19, x17, x18
    li x20, 0x7276dc54
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x19, 0x904c0fae
    li x17, 0x1c248f32
    li x18, 0xdbf46889
    pv.sdotsp.sc.h x19, x17, x18
    li x20, 0x6db9b0b4
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x19, 0x9b444707
    li x17, 0x01dd1d61
    li x18, 0x801c5e19
    pv.sdotsp.sc.h x19, x17, x18
    li x20, 0xa6c01815
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x19, 0x20343ec8
    li x17, 0xb203ff4e
    li x18, 0x4abc4ca3
    pv.sdotsp.sc.h x19, x17, x18
    li x20, 0x08a6315b
    beq x20, x19, test85
    c.addi x15, 0x1
#tests85-90 test the pv.sdotsp.sci.h instruction. values loaded in and compared to are expected output values
#pv.sdotsp.sci.h is of the form "pv.sdotsp.sci.h rD, rs1, Imm6"
test85:
    li x19, 0xaf9f2d53
    li x17, 0xa0bf6c6c
    pv.sdotsp.sci.h x19, x17, 0x0e
    li x20, 0xaf9fe5ad
    beq x20, x19, test86
    c.addi x15, 0x1
test86:
    li x19, 0xf451c0dd
    li x17, 0x11917e9e
    pv.sdotsp.sci.h x19, x17, 0x1c
    li x20, 0xf4618601
    beq x20, x19, test87
    c.addi x15, 0x1
test87:
    li x19, 0x44e772f7
    li x17, 0x21d2135d
    pv.sdotsp.sci.h x19, x17, 0x12
    li x20, 0x44eb3045
    beq x20, x19, test88
    c.addi x15, 0x1
test88:
    li x19, 0x79f4eac9
    li x17, 0xbf947e2a
    pv.sdotsp.sci.h x19, x17, 0x1b
    li x20, 0x79fb6dd3
    beq x20, x19, test89
    c.addi x15, 0x1
test89:
    li x19, 0x54f94a8c
    li x17, 0x97068b1a
    pv.sdotsp.sci.h x19, x17, 0x03
    li x20, 0x54f6b0ec
    beq x20, x19, test90
    c.addi x15, 0x1
test90:
    li x19, 0x57cd79c2
    li x17, 0x44db3c7b
    pv.sdotsp.sci.h x19, x17, 0x0d
    li x20, 0x57d40b20
    beq x20, x19, test91
    c.addi x15, 0x1
#tests91-96 test the pv.sdotsp.b instruction. values loaded in and compared to are expected output values
#pv.sdotsp.b is of the form "pv.sdotsp.b rD, rs1, rs2"
test91:
    li x19, 0x3cbbce34
    li x17, 0x02fb75bc
    li x18, 0xd152ff76
    pv.sdotsp.b x19, x17, x18
    li x20, 0x3cbbac6f
    beq x20, x19, test92
    c.addi x15, 0x1
test92:
    li x19, 0x3ea348d8
    li x17, 0xb7336a6c
    li x18, 0xf24fbc1a
    pv.sdotsp.b x19, x17, x18
    li x20, 0x3ea34b63
    beq x20, x19, test93
    c.addi x15, 0x1
test93:
    li x19, 0x7c6b5bad
    li x17, 0xaa3d6c3f
    li x18, 0x578240e4
    pv.sdotsp.b x19, x17, x18
    li x20, 0x7c6b3489
    beq x20, x19, test94
    c.addi x15, 0x1
test94:
    li x19, 0xd75f4bf1
    li x17, 0xbebd393e
    li x18, 0x3720913c
    pv.sdotsp.b x19, x17, x18
    li x20, 0xd75f2b34
    beq x20, x19, test95
    c.addi x15, 0x1
test95:
    li x19, 0x9ca2df54
    li x17, 0x8a6bc6b7
    li x18, 0x0e996134
    pv.sdotsp.b x19, x17, x18
    li x20, 0x9ca28905
    beq x20, x19, test96
    c.addi x15, 0x1
test96:
    li x19, 0x1f437786
    li x17, 0x35eec174
    li x18, 0x5049b31c
    pv.sdotsp.b x19, x17, x18
    li x20, 0x1f43a297
    beq x20, x19, test97
    c.addi x15, 0x1
#tests97-102 test the pv.sdotsp.sc.b instruction. values loaded in and compared to are expected output values
#pv.sdotsp.sc.b is of the form "pv.sdotsp.sc.b rD, rs1, rs2"
test97:
    li x19, 0x36e5da3f
    li x17, 0x1db6da34
    li x18, 0x1b3a7736
    pv.sdotsp.sc.b x19, x17, x18
    li x20, 0x36e5d3b5
    beq x20, x19, test98
    c.addi x15, 0x1
test98:
    li x19, 0x1850a15f
    li x17, 0x02c6d241
    li x18, 0x0af8642e
    pv.sdotsp.sc.b x19, x17, x18
    li x20, 0x18509ab9
    beq x20, x19, test99
    c.addi x15, 0x1
test99:
    li x19, 0x5515b670
    li x17, 0x5da3634e
    li x18, 0x072c9c19
    pv.sdotsp.sc.b x19, x17, x18
    li x20, 0x5515c7b9
    beq x20, x19, test100
    c.addi x15, 0x1
test100:
    li x19, 0xcbe7832a
    li x17, 0x3c0d1c41
    li x18, 0x5cf64a54
    pv.sdotsp.sc.b x19, x17, x18
    li x20, 0xcbe7b9a2
    beq x20, x19, test101
    c.addi x15, 0x1
test101:
    li x19, 0x84eaf32e
    li x17, 0x9b8c5402
    li x18, 0x1b5c9218
    pv.sdotsp.sc.b x19, x17, x18
    li x20, 0x84eae6e6
    beq x20, x19, test102
    c.addi x15, 0x1
test102:
    li x19, 0x8dea1b9a
    li x17, 0x60aeb8a3
    li x18, 0x58050242
    pv.sdotsp.sc.b x19, x17, x18
    li x20, 0x8de9f4ac
    beq x20, x19, test103
    c.addi x15, 0x1
#tests103-108 test the pv.sdotsp.sci.b instruction. values loaded in and compared to are expected output values
#pv.sdotsp.sci.b is of the form "pv.sdotsp.sci.b rD, rs1, Imm6"
test103:
    li x19, 0x1e5fdb51
    li x17, 0x46e895d9
    pv.sdotsp.sci.b x19, x17, 0x05
    li x20, 0x1e5fd95d
    beq x20, x19, test104
    c.addi x15, 0x1
test104:
    li x19, 0x98debfb8
    li x17, 0x28846a49
    pv.sdotsp.sci.b x19, x17, 0x01
    li x20, 0x98dec017
    beq x20, x19, test105
    c.addi x15, 0x1
test105:
    li x19, 0x59d396ef
    li x17, 0x8f4ffd41
    pv.sdotsp.sci.b x19, x17, 0x12
    li x20, 0x59d398e7
    beq x20, x19, test106
    c.addi x15, 0x1
test106:
    li x19, 0x38574f45
    li x17, 0x547d9f3a
    pv.sdotsp.sci.b x19, x17, 0x18
    li x20, 0x38575f35
    beq x20, x19, test107
    c.addi x15, 0x1
test107:
    li x19, 0xca3bb03a
    li x17, 0xa83cc2f9
    pv.sdotsp.sci.b x19, x17, 0x04
    li x20, 0xca3baeb6
    beq x20, x19, test108
    c.addi x15, 0x1
test108:
    li x19, 0x2185911a
    li x17, 0xc97c4baf
    pv.sdotsp.sci.b x19, x17, 0x10
    li x20, 0x2185950a
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
