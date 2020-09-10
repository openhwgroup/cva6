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
#tests1-6 test the pv.cmpeq.h instruction. values loaded in and compared to are expected output values
#pv.cmpeq.h is of the form "pv.cmpeq.h rD, rs1, rs2".
test1:
    li x17, 0x1d2a938d
    li x18, 0xaa03938d
    pv.cmpeq.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0x6da6b594
    li x18, 0x6da60ac2
    pv.cmpeq.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0x4d419302
    li x18, 0xe6223401
    pv.cmpeq.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x09100c36
    li x18, 0x09100c36
    pv.cmpeq.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0xdf4e73e7
    li x18, 0x051fb62f
    pv.cmpeq.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0xd6d3feb8
    li x18, 0xd6d3feb8
    pv.cmpeq.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the pv.cmpeq.sc.h instruction. values loaded in and compared to are expected output values
#pv.cmpeq.sc.h is of the form "pv.cmpeq.sc.h rD, rs1, rs2".
test7:
    li x17, 0xa2d86f51
    li x18, 0x15b7a2d8
    pv.cmpeq.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x00050005
    li x18, 0xc7590005
    pv.cmpeq.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0xb47fb60d
    li x18, 0xa5c2c65a
    pv.cmpeq.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0x7633579b
    li x18, 0xea56579b
    pv.cmpeq.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0xb2b390f1
    li x18, 0xbaa750e2
    pv.cmpeq.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0xbef9bef9
    li x18, 0x338fbef9
    pv.cmpeq.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the pv.cmpeq.sci.h instruction. values loaded in and compared to are expected output values
#pv.cmpeq.sci.h is of the form "pv.cmpeq.sci.h rD, rs1, Imm6".
test13:
    li x17, 0x001f001f
    pv.cmpeq.sci.h x19, x17, 0x1f
    li x20, 0xffffffff
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0x8f58bb58
    pv.cmpeq.sci.h x19, x17, 0x6
    li x20, 0x00000000
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0xb844000c
    pv.cmpeq.sci.h x19, x17, 0xc
    li x20, 0x0000ffff
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0x0013c0f3
    pv.cmpeq.sci.h x19, x17, 0x13
    li x20, 0xffff0000
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x94342983
    pv.cmpeq.sci.h x19, x17, 0x2
    li x20, 0x00000000
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x001a001a
    pv.cmpeq.sci.h x19, x17, 0x1a
    li x20, 0xffffffff
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the pv.cmpeq.b instruction. values loaded in and compared to are expected output values
#pv.cmpeq.b is of the form "pv.cmpeq.b rD, rs1, rs2".
test19:
    li x17, 0xfee6cd15
    li x18, 0xc9f2cdb9
    pv.cmpeq.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0x43fb42ed
    li x18, 0x43b04296
    pv.cmpeq.b x19, x17, x18
    li x20, 0xff00ff00
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0xd2b683d5
    li x18, 0xcbb6c3d5
    pv.cmpeq.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0xb5b28f18
    li x18, 0x2c0bdfd3
    pv.cmpeq.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0x1a7d74c4
    li x18, 0x1a7d74c4
    pv.cmpeq.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0x2035e686
    li x18, 0x3f060e86
    pv.cmpeq.b x19, x17, x18
    li x20, 0x000000ff
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the pv.cmpeq.sc.b instruction. values loaded in and compared to are expected output values
#pv.cmpeq.sc.b is of the form "pv.cmpeq.sc.b rD, rs1, rs2".
test25:
    li x17, 0xa28b3ea7
    li x18, 0x51b2f630
    pv.cmpeq.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x5cdd3e28
    li x18, 0xd2fb313e
    pv.cmpeq.sc.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0xf5f52966
    li x18, 0xd4d9f3f5
    pv.cmpeq.sc.b x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0xbe0fe6f9
    li x18, 0x044266f9
    pv.cmpeq.sc.b x19, x17, x18
    li x20, 0x000000ff
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0xcc31c821
    li x18, 0xa9901831
    pv.cmpeq.sc.b x19, x17, x18
    li x20, 0x00ff0000
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0xc9fa59f5
    li x18, 0x15763ead
    pv.cmpeq.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the pv.cmpeq.sci.b instruction. values loaded in and compared to are expected output values
#pv.cmpeq.sci.b is of the form "pv.cmpeq.sci.b rD, rs1, Imm6".
test31:
    li x17, 0xed12fe15
    pv.cmpeq.sci.b x19, x17, 0x12
    li x20, 0x00ff0000
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0x0cda0cf8
    pv.cmpeq.sci.b x19, x17, 0xc
    li x20, 0xff00ff00
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0x7ce82910
    pv.cmpeq.sci.b x19, x17, 0x10
    li x20, 0x000000ff
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0x1369a5dd
    pv.cmpeq.sci.b x19, x17, 0x13
    li x20, 0xff000000
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x589d054c
    pv.cmpeq.sci.b x19, x17, 0x5
    li x20, 0x0000ff00
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0xe91d13f0
    pv.cmpeq.sci.b x19, x17, 0x1d
    li x20, 0x00ff0000
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the pv.cmpne.h instruction. values loaded in and compared to are expected output values
#pv.cmpne.h is of the form "pv.cmpne.h rD, rs1, rs2".
test37:
    li x17, 0xccb9afed
    li x18, 0x8a3aafed
    pv.cmpne.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0xf3c8ea33
    li x18, 0x0d6b2784
    pv.cmpne.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0x6787bc36
    li x18, 0x6787c2d3
    pv.cmpne.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x9846ba87
    li x18, 0x9846ba87
    pv.cmpne.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0x498ebcca
    li x18, 0x421f637d
    pv.cmpne.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0xc71757b2
    li x18, 0xfd1757b2
    pv.cmpne.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the pv.cmpne.sc.h instruction. values loaded in and compared to are expected output values
#pv.cmpne.sc.h is of the form "pv.cmpne.sc.h rD, rs1, rs2".
test43:
    li x17, 0x74cd74cd
    li x18, 0xe55374cd
    pv.cmpne.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0xaa223487
    li x18, 0x58dc1fa0
    pv.cmpne.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0x23a4a348
    li x18, 0xba86a348
    pv.cmpne.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0xf67abc9b
    li x18, 0x3328f67a
    pv.cmpne.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0x89123bce
    li x18, 0x46cd2f98
    pv.cmpne.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0xa4293948
    li x18, 0x9c8fa429
    pv.cmpne.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the pv.cmpne.sci.h instruction. values loaded in and compared to are expected output values
#pv.cmpne.sci.h is of the form "pv.cmpne.sci.h rD, rs1, Imm6".
test49:
    li x17, 0x000dd435
    pv.cmpne.sci.h x19, x17, 0xd
    li x20, 0x0000ffff
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0xb8b00007
    pv.cmpne.sci.h x19, x17, 0x7
    li x20, 0xffff0000
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0x00020002
    pv.cmpne.sci.h x19, x17, 0x2
    li x20, 0x00000000
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0xeddec921
    pv.cmpne.sci.h x19, x17, 0x1c
    li x20, 0xffffffff
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0x6ec839dc
    pv.cmpne.sci.h x19, x17, 0x10
    li x20, 0xffffffff
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0x0000bb4d
    pv.cmpne.sci.h x19, x17, 0x0
    li x20, 0x0000ffff
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the pv.cmpne.b instruction. values loaded in and compared to are expected output values
#pv.cmpne.b is of the form "pv.cmpne.b rD, rs1, rs2".
test55:
    li x17, 0xdd169b17
    li x18, 0xe516aa17
    pv.cmpne.b x19, x17, x18
    li x20, 0xff00ff00
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0xcb8b9b20
    li x18, 0x68f03c20
    pv.cmpne.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0xbc7cc2d8
    li x18, 0xbcebc2b2
    pv.cmpne.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0xc7cb9312
    li x18, 0xc37660fe
    pv.cmpne.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0x4dd1a689
    li x18, 0x2ed19c56
    pv.cmpne.b x19, x17, x18
    li x20, 0xff00ffff
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0xfbe84fba
    li x18, 0xfbe84fba
    pv.cmpne.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the pv.cmpne.sc.b instruction. values loaded in and compared to are expected output values
#pv.cmpne.sc.b is of the form "pv.cmpne.sc.b rD, rs1, rs2".
test61:
    li x17, 0x5ed61df5
    li x18, 0xc5e8bf27
    pv.cmpne.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0x8a5df68a
    li x18, 0xfb21de8a
    pv.cmpne.sc.b x19, x17, x18
    li x20, 0x00ffff00
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0x9f735394
    li x18, 0x7d19d373
    pv.cmpne.sc.b x19, x17, x18
    li x20, 0xff00ffff
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0xeeeeeeee
    li x18, 0x05fb8dee
    pv.cmpne.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0xa4b80b27
    li x18, 0x689cb3a4
    pv.cmpne.sc.b x19, x17, x18
    li x20, 0x00ffffff
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0xc55fcd80
    li x18, 0x6d059863
    pv.cmpne.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the pv.cmpne.sci.b instruction. values loaded in and compared to are expected output values
#pv.cmpne.sci.b is of the form "pv.cmpne.sci.b rD, rs1, Imm6".
test67:
    li x17, 0x0a38ff0a
    pv.cmpne.sci.b x19, x17, 0xa
    li x20, 0x00ffff00
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0x188ca729
    pv.cmpne.sci.b x19, x17, 0x18
    li x20, 0x00ffffff
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0xb41e26b8
    pv.cmpne.sci.b x19, x17, 0x1e
    li x20, 0xff00ffff
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x36fe4c86
    pv.cmpne.sci.b x19, x17, 0x05
    li x20, 0xffffffff
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0xa8cf1414
    pv.cmpne.sci.b x19, x17, 0x14
    li x20, 0xffff0000
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0xf897437e
    pv.cmpne.sci.b x19, x17, 0x8
    li x20, 0xffffffff
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the pv.cmpgt.h instruction. values loaded in and compared to are expected output values
#pv.cmpgt.h is of the form "pv.cmpgt.h rD, rs1, rs2".
test73:
    li x17, 0x40fc86fa
    li x18, 0xf486b68f
    pv.cmpgt.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x17, 0xeda80242
    li x18, 0x20cbcb80
    pv.cmpgt.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x17, 0xbe0668b4
    li x18, 0xce3c764e
    pv.cmpgt.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x17, 0xe2958a37
    li x18, 0x2b944692
    pv.cmpgt.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x17, 0xeaa9d9ca
    li x18, 0x7d98411e
    pv.cmpgt.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x17, 0x724566f4
    li x18, 0x3e90dbe6
    pv.cmpgt.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the pv.cmpgt.sc.h instruction. values loaded in and compared to are expected output values
#pv.cmpgt.sc.h is of the form "pv.cmpgt.sc.h rD, rs1, rs2".
test79:
    li x17, 0x3e998a14
    li x18, 0xd8c9e031
    pv.cmpgt.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x17, 0x568d1d04
    li x18, 0xebacff17
    pv.cmpgt.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x17, 0xb27b96f5
    li x18, 0x21d49a39
    pv.cmpgt.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x17, 0x9c251041
    li x18, 0x03432a7a
    pv.cmpgt.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x17, 0x20a4d96c
    li x18, 0x5f3fd12b
    pv.cmpgt.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x17, 0xbd6234c6
    li x18, 0x354a2d37
    pv.cmpgt.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test85
    c.addi x15, 0x1
#tests85-90 test the pv.cmpgt.sci.h instruction. values loaded in and compared to are expected output values
#pv.cmpgt.sci.h is of the form "pv.cmpgt.sci.h rD, rs1, Imm6".
test85:
    li x17, 0x57dbe7cb
    pv.cmpgt.sci.h x19, x17, 0x1d
    li x20, 0xffff0000
    beq x20, x19, test86
    c.addi x15, 0x1
test86:
    li x17, 0x86fe7a69
    pv.cmpgt.sci.h x19, x17, 0x1
    li x20, 0x0000ffff
    beq x20, x19, test87
    c.addi x15, 0x1
test87:
    li x17, 0x2d417975
    pv.cmpgt.sci.h x19, x17, 0x5
    li x20, 0xffffffff
    beq x20, x19, test88
    c.addi x15, 0x1
test88:
    li x17, 0xc586f391
    pv.cmpgt.sci.h x19, x17, 0x18
    li x20, 0x00000000
    beq x20, x19, test89
    c.addi x15, 0x1
test89:
    li x17, 0x38ccf127
    pv.cmpgt.sci.h x19, x17, 0x09
    li x20, 0xffff0000
    beq x20, x19, test90
    c.addi x15, 0x1
test90:
    li x17, 0xba393def
    pv.cmpgt.sci.h x19, x17, 0x1f
    li x20, 0x0000ffff
    beq x20, x19, test91
    c.addi x15, 0x1
#tests91-96 test the pv.cmpgt.b instruction. values loaded in and compared to are expected output values
#pv.cmpgt.b is of the form "pv.cmpgt.b rD, rs1, rs2".
test91:
    li x17, 0x60af9b4c
    li x18, 0x14e66ee2
    pv.cmpgt.b x19, x17, x18
    li x20, 0xff0000ff
    beq x20, x19, test92
    c.addi x15, 0x1
test92:
    li x17, 0xca6b0531
    li x18, 0xca160400
    pv.cmpgt.b x19, x17, x18
    li x20, 0x00ffffff
    beq x20, x19, test93
    c.addi x15, 0x1
test93:
    li x17, 0xb10797a0
    li x18, 0xad45142d
    pv.cmpgt.b x19, x17, x18
    li x20, 0xff000000
    beq x20, x19, test94
    c.addi x15, 0x1
test94:
    li x17, 0x606d888a
    li x18, 0x41fe0c9b
    pv.cmpgt.b x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test95
    c.addi x15, 0x1
test95:
    li x17, 0xbd53fe09
    li x18, 0x1a57ec32
    pv.cmpgt.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test96
    c.addi x15, 0x1
test96:
    li x17, 0x73d9119a
    li x18, 0x9fb04c88
    pv.cmpgt.b x19, x17, x18
    li x20, 0xffff00ff
    beq x20, x19, test97
    c.addi x15, 0x1
#tests97-102 test the pv.cmpgt.sc.b instruction. values loaded in and compared to are expected output values
#pv.cmpgt.sc.b is of the form "pv.cmpgt.sc.b rD, rs1, rs2".
test97:
    li x17, 0xc276014e
    li x18, 0x71ccf7ed
    pv.cmpgt.sc.b x19, x17, x18
    li x20, 0x00ffffff
    beq x20, x19, test98
    c.addi x15, 0x1
test98:
    li x17, 0x1abed23a
    li x18, 0x05dccdb7
    pv.cmpgt.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test99
    c.addi x15, 0x1
test99:
    li x17, 0x23af7d6b
    li x18, 0xb833437d
    pv.cmpgt.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test100
    c.addi x15, 0x1
test100:
    li x17, 0x6f15f401
    li x18, 0x174b810c
    pv.cmpgt.sc.b x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test101
    c.addi x15, 0x1
test101:
    li x17, 0xb714168f
    li x18, 0x4b278418
    pv.cmpgt.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test102
    c.addi x15, 0x1
test102:
    li x17, 0x4be75c36
    li x18, 0xc4011682
    pv.cmpgt.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test103
    c.addi x15, 0x1
#tests103-108 test the pv.cmpgt.sci.b instruction. values loaded in and compared to are expected output values
#pv.cmpgt.sci.b is of the form "pv.cmpgt.sci.b rD, rs1, Imm6".
test103:
    li x17, 0x2da42ff0
    pv.cmpgt.sci.b x19, x17, 0x12
    li x20, 0xff00ff00
    beq x20, x19, test104
    c.addi x15, 0x1
test104:
    li x17, 0x6dfaabd3
    pv.cmpgt.sci.b x19, x17, 0x4
    li x20, 0xff000000
    beq x20, x19, test105
    c.addi x15, 0x1
test105:
    li x17, 0xd51caa3b
    pv.cmpgt.sci.b x19, x17, 0x1c
    li x20, 0x000000ff
    beq x20, x19, test106
    c.addi x15, 0x1
test106:
    li x17, 0x8d812c93
    pv.cmpgt.sci.b x19, x17, 0x9
    li x20, 0x0000ff00
    beq x20, x19, test107
    c.addi x15, 0x1
test107:
    li x17, 0x1fa82884
    pv.cmpgt.sci.b x19, x17, 0xf
    li x20, 0xff00ff00
    beq x20, x19, test108
    c.addi x15, 0x1
test108:
    li x17, 0x7abd8b42
    pv.cmpgt.sci.b x19, x17, 0x1d
    li x20, 0xff0000ff
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
