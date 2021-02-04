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
    li x31, 0x5911efde
    li x4, 0x40001104
#tests1-6 test the pv.subrotmj instruction. values loaded in and compared to are expected output values
#pv.subrotmj is of the form "pv.subrotmj rD, rs1, rs2". rD[15:0] = rs1[31:16]-rs2[31:16],
#rD[31:16] = rs2[15:0]-rs1[15:0]
test1:
    li x17, 0xaf2d2f97
    li x18, 0x6dc18787
    .word 0x6d2889d7    #pv.subrotmj x19, x17, x18
    li x20, 0x57f0416c
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x109bf3c5
    li x18, 0x1acfd8f6
    .word 0x6d2889d7    #pv.subrotmj x19, x17, x18
    li x20, 0xe531f5cc
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0x24e9d2ae
    li x18, 0x304f5001
    .word 0x6d2889d7    #pv.subrotmj x19, x17, x18
    li x20, 0x7d53f49a
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0xa0ffa6e4
    li x18, 0x02d8668b
    .word 0x6d2889d7    #pv.subrotmj x19, x17, x18
    li x20, 0xbfa79e27
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0x6b3808fe
    li x18, 0x73ce484a
    .word 0x6d2889d7    #pv.subrotmj x19, x17, x18
    li x20, 0x3f4cf76a
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x054c2c63
    li x18, 0x2f2e30c2
    .word 0x6d2889d7    #pv.subrotmj x19, x17, x18
    li x20, 0x045fd61e
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.subrotmj.div2 instruction. values loaded in and compared to are expected output values
#pv.subrotmj.div2 is of the form "pv.subrotmj.div2 rD, rs1, rs2". rD[15:0] = (rs1[31:16]-rs2[31:16])>>1,
#rD[31:16] = (rs2[15:0]-rs1[15:0])>>1
test7:
    li x17, 0xf630bfb4
    li x18, 0xcffa4336
    .word 0x6d28a9d7    #pv.subrotmj.div2 x19, x17, x18
    li x20, 0xc1c1131b
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x3f433b1e
    li x18, 0x809492e2
    .word 0x6d28a9d7    #pv.subrotmj.div2 x19, x17, x18
    li x20, 0x2be2df57
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0xbe812610
    li x18, 0x8eae076d
    .word 0x6d28a9d7    #pv.subrotmj.div2 x19, x17, x18
    li x20, 0xf0ae17e9
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0x8893401d
    li x18, 0x0a586318
    .word 0x6d28a9d7    #pv.subrotmj.div2 x19, x17, x18
    li x20, 0x117d3f1d
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0x6fb8bcd2
    li x18, 0x24070fca
    .word 0x6d28a9d7    #pv.subrotmj.div2 x19, x17, x18
    li x20, 0x297c25d8
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x4c43c1f4
    li x18, 0x66d3202f
    .word 0x6d28a9d7    #pv.subrotmj.div2 x19, x17, x18
    li x20, 0x2f1df2b8
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.subrotmj.div4 instruction. values loaded in and compared to are expected output values
#pv.subrotmj.div4 is of the form "pv.subrotmj.div4 rD, rs1, rs2". rD[15:0] = (rs1[31:16]-rs2[31:16])>>2,
#rD[31:16] = (rs2[15:0]-rs1[15:0])>>2
test13:
    li x17, 0x1bff7f6e
    li x18, 0x38092ba1
    .word 0x6d28c9d7    #pv.subrotmj.div4 x19, x17, x18
    li x20, 0xeb0cf8fd
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0xd85d23e9
    li x18, 0xcf4da1d1
    .word 0x6d28c9d7    #pv.subrotmj.div4 x19, x17, x18
    li x20, 0x1f7a0244
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0xdb922fd6
    li x18, 0x101ecbe1
    .word 0x6d28c9d7    #pv.subrotmj.div4 x19, x17, x18
    li x20, 0xe702f2dd
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0x412fc401
    li x18, 0x3f26c504
    .word 0x6d28c9d7    #pv.subrotmj.div4 x19, x17, x18
    li x20, 0x00400082
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x54cdba63
    li x18, 0x62a71824
    .word 0x6d28c9d7    #pv.subrotmj.div4 x19, x17, x18
    li x20, 0x1770fc89
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0xe35cadaa
    li x18, 0xbd884bda
    .word 0x6d28c9d7    #pv.subrotmj.div4 x19, x17, x18
    li x20, 0xe78c0975
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.subrotmj.div8 instruction. values loaded in and compared to are expected output values
#pv.subrotmj.div8 is of the form "pv.subrotmj.div8 rD, rs1, rs2". rD[15:0] = (rs1[31:16]-rs2[31:16])>>3,
#rD[31:16] = (rs2[15:0]-rs1[15:0])>>3
test19:
    li x17, 0xb75b6f5c
    li x18, 0x7ee6e76d
    .word 0x6d28e9d7    #pv.subrotmj.div8 x19, x17, x18
    li x20, 0x0f02070e
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x41d543eb
    li x18, 0x5790d5de
    .word 0x6d28e9d7    #pv.subrotmj.div8 x19, x17, x18
    li x20, 0xf23efd48
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0x03b28e4e
    li x18, 0x157426c4
    .word 0x6d28e9d7    #pv.subrotmj.div8 x19, x17, x18
    li x20, 0xf30efdc7
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0xcc07813c
    li x18, 0x1e911df9
    .word 0x6d28e9d7    #pv.subrotmj.div8 x19, x17, x18
    li x20, 0xf397f5ae
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0xfbab5801
    li x18, 0xe8a2bbd0
    .word 0x6d28e9d7    #pv.subrotmj.div8 x19, x17, x18
    li x20, 0x0c790261
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0x2e098dc4
    li x18, 0xeaf898b2
    .word 0x6d28e9d7    #pv.subrotmj.div8 x19, x17, x18
    li x20, 0x015d0862
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.cplxconj instruction. values loaded in and compared to are expected output values
#pv.cplxconj is of the form "pv.cplxconj rD, rs1".
test25:
    li x17, 0x8442ad8e
    .word 0x5c0889d7    #pv.cplxconj x19, x17
    li x20, 0x7bbead8e
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x66cd7991
    .word 0x5c0889d7    #pv.cplxconj x19, x17
    li x20, 0x99337991
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0x49849965
    .word 0x5c0889d7    #pv.cplxconj x19, x17
    li x20, 0xb67c9965
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0x21367b6b
    .word 0x5c0889d7    #pv.cplxconj x19, x17
    li x20, 0xdeca7b6b
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0x1477100a
    .word 0x5c0889d7    #pv.cplxconj x19, x17
    li x20, 0xeb89100a
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0xa615f8ce
    .word 0x5c0889d7    #pv.cplxconj x19, x17
    li x20, 0x59ebf8ce
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.cplxmul.r instruction. values loaded in and compared to are expected output values
#pv.cplxmul.r is of the form "pv.cplxmul.r rD, rs1, rs2".
test31:
    li x19, 0xe093a374
    li x17, 0x68c48474
    li x18, 0xb5a735b7
    .word 0x552889d7    #pv.cplxmul.r x19, x17, x18
    li x20, 0xe0930901
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x19, 0xbb90ae84
    li x17, 0x3862897a
    li x18, 0xae76a3dc
    .word 0x552889d7    #pv.cplxmul.r x19, x17, x18
    li x20, 0xbb90793c
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x19, 0x25cc94b3
    li x17, 0xb7cbb7dc
    li x18, 0x71df311a
    .word 0x552889d7    #pv.cplxmul.r x19, x17, x18
    li x20, 0x25cc2490
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x19, 0x4b0b9796
    li x17, 0xee3c5a30
    li x18, 0x9629081b
    .word 0x552889d7    #pv.cplxmul.r x19, x17, x18
    li x20, 0x4b0bf705
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x19, 0x0e7c05a1
    li x17, 0xfa556505
    li x18, 0x1e1e9e99
    .word 0x552889d7    #pv.cplxmul.r x19, x17, x18
    li x20, 0x0e7cb476
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x19, 0x0c50fd6d
    li x17, 0x1c198900
    li x18, 0x16a779a5
    .word 0x552889d7    #pv.cplxmul.r x19, x17, x18
    li x20, 0x0c5089ef
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.cplxmul.r.div2 instruction. values loaded in and compared to are expected output values
#pv.cplxmul.r.div2 is of the form "pv.cplxmul.r.div2 rD, rs1, rs2".
test37:
    li x19, 0xf2d306f0
    li x17, 0xb188c359
    li x18, 0x58ba54ab
    .word 0x5528a9d7    #pv.cplxmul.r.div2 x19, x17, x18
    li x20, 0xf2d30722
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x19, 0x7c9674fd
    li x17, 0xa1441f2b
    li x18, 0xad8ac34a
    .word 0x5528a9d7    #pv.cplxmul.r.div2 x19, x17, x18
    li x20, 0x7c96da17
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x19, 0x2d033231
    li x17, 0x5480e56e
    li x18, 0x829107fb
    .word 0x5528a9d7    #pv.cplxmul.r.div2 x19, x17, x18
    li x20, 0x2d032893
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x19, 0xec097a26
    li x17, 0x7737ce12
    li x18, 0x5af57d71
    .word 0x5528a9d7    #pv.cplxmul.r.div2 x19, x17, x18
    li x20, 0xec09bd2d
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x19, 0x68ef850a
    li x17, 0x7e7caf49
    li x18, 0x48b48c84
    .word 0x5528a9d7    #pv.cplxmul.r.div2 x19, x17, x18
    li x20, 0x68ef007d
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x19, 0x2e16d229
    li x17, 0x09f38f2a
    li x18, 0x67e4f120
    .word 0x5528a9d7    #pv.cplxmul.r.div2 x19, x17, x18
    li x20, 0x2e160284
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.cplxmul.r.div4 instruction. values loaded in and compared to are expected output values
#pv.cplxmul.r.div4 is of the form "pv.cplxmul.r.div4 rD, rs1, rs2".
test43:
    li x19, 0x68dc4d8d
    li x17, 0xd81aa079
    li x18, 0x1b333d39
    .word 0x5528c9d7    #pv.cplxmul.r.div4 x19, x17, x18
    li x20, 0x68dcf6b2
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x19, 0xcaac8fcb
    li x17, 0xb7062e88
    li x18, 0x804905e9
    .word 0x5528c9d7    #pv.cplxmul.r.div4 x19, x17, x18
    li x20, 0xcaacee55
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x19, 0x1301e0bb
    li x17, 0xa54d96d4
    li x18, 0x327ac09b
    .word 0x5528c9d7    #pv.cplxmul.r.div4 x19, x17, x18
    li x20, 0x130115f6
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x19, 0xf8bda6a1
    li x17, 0xad3b3d23
    li x18, 0xf388c2ac
    .word 0x5528c9d7    #pv.cplxmul.r.div4 x19, x17, x18
    li x20, 0xf8bdf6a9
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x19, 0x1b17aad1
    li x17, 0x02cda197
    li x18, 0xc953f6b1
    .word 0x5528c9d7    #pv.cplxmul.r.div4 x19, x17, x18
    li x20, 0x1b170203
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x19, 0x7dad1aac
    li x17, 0xeb187f17
    li x18, 0xfc758e75
    .word 0x5528c9d7    #pv.cplxmul.r.div4 x19, x17, x18
    li x20, 0x7dade3ab
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.cplxmul.r.div8 instruction. values loaded in and compared to are expected output values
#pv.cplxmul.r.div8 is of the form "pv.cplxmul.r.div8 rD, rs1, rs2".
test49:
    li x19, 0x52271eb6
    li x17, 0xec34072f
    li x18, 0xe05ad5c9
    .word 0x5528e9d7    #pv.cplxmul.r.div8 x19, x17, x18
    li x20, 0x5227ff17
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x19, 0xa25b2a08
    li x17, 0x4a0eed30
    li x18, 0x641bea8e
    .word 0x5528e9d7    #pv.cplxmul.r.div8 x19, x17, x18
    li x20, 0xa25bf927
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x19, 0x83407d59
    li x17, 0x3a940235
    li x18, 0x8fcc3806
    .word 0x5528e9d7    #pv.cplxmul.r.div8 x19, x17, x18
    li x20, 0x8340068a
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x19, 0x23a5a7b8
    li x17, 0xe447bb1a
    li x18, 0xcec233e9
    .word 0x5528e9d7    #pv.cplxmul.r.div8 x19, x17, x18
    li x20, 0x23a5fb2c
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x19, 0x9f032bb7
    li x17, 0x4c06d0db
    li x18, 0x49c9231d
    .word 0x5528e9d7    #pv.cplxmul.r.div8 x19, x17, x18
    li x20, 0x9f03f8e7
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x19, 0xb03076a9
    li x17, 0x5b349c89
    li x18, 0x16d3f8c5
    .word 0x5528e9d7    #pv.cplxmul.r.div8 x19, x17, x18
    li x20, 0xb030feab
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.cplxmul.i instruction. values loaded in and compared to are expected output values
#pv.cplxmul.i is of the form "pv.cplxmul.i.div2 rD, rs1, rs2".
test55:
    li x19, 0x74f95d16
    li x17, 0x13c99767
    li x18, 0x49fdbc20
    .word 0x572889d7    #pv.cplxmul.i x19, x17, x18
    li x20, 0xb90c5d16
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x19, 0x89b50197
    li x17, 0xc8de8cef
    li x18, 0xb46b8232
    .word 0x572889d7    #pv.cplxmul.i x19, x17, x18
    li x20, 0x7a210197
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x19, 0xd927e9de
    li x17, 0x0dd4ce08
    li x18, 0xf258bdea
    .word 0x572889d7    #pv.cplxmul.i x19, x17, x18
    li x20, 0xfe31e9de
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x19, 0x9e9eb3ef
    li x17, 0x6d97b987
    li x18, 0x1bf24f6e
    .word 0x572889d7    #pv.cplxmul.i x19, x17, x18
    li x20, 0x349eb3ef
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x19, 0x1630bd14
    li x17, 0x158ea724
    li x18, 0x7ea93025
    .word 0x572889d7    #pv.cplxmul.i x19, x17, x18
    li x20, 0xb02dbd14
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x19, 0xc43932b4
    li x17, 0xf67d173b
    li x18, 0x8c470b5b
    .word 0x572889d7    #pv.cplxmul.i x19, x17, x18
    li x20, 0xea2732b4
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.cplxmul.i.div2 instruction. values loaded in and compared to are expected output values
#pv.cplxmul.i.div2 is of the form "pv.cplxmul.i.div2 rD, rs1, rs2".
test61:
    li x19, 0x93da3581
    li x17, 0xf58e6a19
    li x18, 0xbd76f586
    .word 0x5728a9d7    #pv.cplxmul.i.div2 x19, x17, x18
    li x20, 0xe4d93581
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x19, 0x2feac4d4
    li x17, 0xb7d1d296
    li x18, 0xe603c7b5
    .word 0x5728a9d7    #pv.cplxmul.i.div2 x19, x17, x18
    li x20, 0x147bc4d4
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x19, 0x2c645321
    li x17, 0xea6727f5
    li x18, 0x2394b319
    .word 0x5728a9d7    #pv.cplxmul.i.div2 x19, x17, x18
    li x20, 0x0c0a5321
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x19, 0xc4b99188
    li x17, 0xb62f1e31
    li x18, 0x3af596fa
    .word 0x5728a9d7    #pv.cplxmul.i.div2 x19, x17, x18
    li x20, 0x253c9188
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x19, 0x0ec2cba9
    li x17, 0xc3fb0f53
    li x18, 0x984b363b
    .word 0x5728a9d7    #pv.cplxmul.i.div2 x19, x17, x18
    li x20, 0xed13cba9
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x19, 0xd212d156
    li x17, 0x9e5dfeb9
    li x18, 0x5f95a943
    .word 0x5728a9d7    #pv.cplxmul.i.div2 x19, x17, x18
    li x20, 0x209ad156
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.cplxmul.i.div4 instruction. values loaded in and compared to are expected output values
#pv.cplxmul.i.div4 is of the form "pv.cplxmul.i.div4 rD, rs1, rs2".
test67:
    li x19, 0x3d497610
    li x17, 0xe61d23c5
    li x18, 0x07764e8c
    .word 0x5728c9d7    #pv.cplxmul.i.div4 x19, x17, x18
    li x20, 0xfc8c7610
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x19, 0xb15f4484
    li x17, 0xd11f623c
    li x18, 0xcb030d7d
    .word 0x5728c9d7    #pv.cplxmul.i.div4 x19, x17, x18
    li x20, 0xf4994484
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x19, 0x1a3c19f8
    li x17, 0x746bbe56
    li x18, 0x86370b92
    .word 0x5728c9d7    #pv.cplxmul.i.div4 x19, x17, x18
    li x20, 0x123f19f8
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x19, 0xbbaf71d3
    li x17, 0x88547464
    li x18, 0x5c5c8b42
    .word 0x5728c9d7    #pv.cplxmul.i.div4 x19, x17, x18
    li x20, 0x304871d3
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x19, 0x68960022
    li x17, 0xbb7a7372
    li x18, 0x3447029e
    .word 0x5728c9d7    #pv.cplxmul.i.div4 x19, x17, x18
    li x20, 0x0b6f0022
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x19, 0xd1af248d
    li x17, 0x95c7029d
    li x18, 0x0457e346
    .word 0x5728c9d7    #pv.cplxmul.i.div4 x19, x17, x18
    li x20, 0x05fb248d
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.cplxmul.i.div8 instruction. values loaded in and compared to are expected output values
#pv.cplxmul.i.div8 is of the form "pv.cplxmul.i.div8 rD, rs1, rs2".
test73:
    li x19, 0x9dd06f4f
    li x17, 0x80356c34
    li x18, 0x4dcf2b10
    .word 0x5728e9d7    #pv.cplxmul.i.div8 x19, x17, x18
    li x20, 0x02d96f4f
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x19, 0x8bb89d46
    li x17, 0x2bd857cb
    li x18, 0xdfb54df1
    .word 0x5728e9d7    #pv.cplxmul.i.div8 x19, x17, x18
    li x20, 0x00919d46
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x19, 0xee4604ec
    li x17, 0xc7b2c6ec
    li x18, 0x9f2505fb
    .word 0x5728e9d7    #pv.cplxmul.i.div8 x19, x17, x18
    li x20, 0x051104ec
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x19, 0x68619b42
    li x17, 0xa102a05e
    li x18, 0x604a0eb0
    .word 0x5728e9d7    #pv.cplxmul.i.div8 x19, x17, x18
    li x20, 0xf5a59b42
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x19, 0x52d8aa89
    li x17, 0xea6ac15d
    li x18, 0x707ad99d
    .word 0x5728e9d7    #pv.cplxmul.i.div8 x19, x17, x18
    li x20, 0xf9edaa89
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x19, 0xf6489edd
    li x17, 0x0b5fab1d
    li x18, 0xe22b4542
    .word 0x5728e9d7    #pv.cplxmul.i.div8 x19, x17, x18
    li x20, 0x033d9edd
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
