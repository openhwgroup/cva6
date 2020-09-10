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
#tests all bit manipulation instructions. NOTE: value of register x15 at the end of the test is the error count
#NOTE: value loaded into x19 prior to the beq instruction in each test is the expected output value
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
#tests1-6 test the p.extract instruction. values loaded in and compared to are expected output values
#p.extract instruction is of format "p.extract rD, rs1, ls3, ls2". ls2 defines the location of the LSB
#that is extracted, while ls3 defines the number of bits that are extracted. answer is sign extended
#based upon the MSB of the extracted value rD = Sext((rs1 & ((1 << (ls3 + 1)) - 1) << ls2) >> ls2), (ls2+ls3)<=32
test1:
    li x20, 0x12577823
    p.extract x18, x20, 7, 24
    li x19, 0x12
    beq x18, x19, test2
    c.addi x15, 0x1
test2:
    li x20, 0x85763245
    p.extract x18, x20, 0, 31
    li x19, 0xffffffff
    beq x18, x19, test3
    c.addi x15, 0x1
test3:
    li x20, 0x69879573
    p.extract x18, x20, 7, 0
    li x19, 0x73
    beq x18, x19, test4
    c.addi x15, 0x1
test4:
    li x20, 0x12577823
    p.extract x18, x20, 0, 0
    li x19, 0xffffffff
    beq x18, x19, test5
    c.addi x15, 0x1
test5:
    li x20, 0x34667485
    p.extract x18, x20, 7, 16
    li x19, 0x66
    beq x18, x19, test6
    c.addi x15, 0x1
test6:
    li x20, 0x78729209
    p.extract x18, x20, 15, 2
    li x19, 0xffffa482
    beq x18, x19, test7
    c.addi x15, 0x1
#tests7-12 test the p.extractu instruction. values loaded in and compared to are expected output values
#p.extractu instruction is of format "p.extractu rD, rs1, ls3, ls2". ls2 defines the location of the LSB
#that is extracted, while ls3 defines the number of bits that are extracted. answer is zero extended
#based upon the MSB of the extracted value rD = Zext((rs1 & ((1 << (ls3 + 1)) -1) << ls2) >> ls2), (ls2+ls3)<=32
test7:
    li x20, 0x12577823
    p.extractu x18, x20, 7, 24
    li x19, 0x12
    beq x18, x19, test8
    c.addi x15, 0x1
test8:
    li x20, 0x85763245
    p.extractu x18, x20, 0, 31
    li x19, 0x1
    beq x18, x19, test9
    c.addi x15, 0x1
test9:
    li x20, 0x69879573
    p.extractu x18, x20, 7, 0
    li x19, 0x73
    beq x18, x19, test10
    c.addi x15, 0x1
test10:
    li x20, 0x12577823
    p.extractu x18, x20, 0, 0
    li x19, 0x1
    beq x18, x19, test11
    c.addi x15, 0x1
test11:
    li x20, 0x34667485
    p.extractu x18, x20, 7, 16
    li x19, 0x66
    beq x18, x19, test12
    c.addi x15, 0x1
test12:
    li x20, 0x78729209
    p.extractu x18, x20, 15, 2
    li x19, 0xa482
    beq x18, x19, test13
    c.addi x15, 0x1
    j test13
#tests13-18 test the p.extractr instruction. values loaded in and compared to are expected output values
#p.extractr instruction is of format "p.extractu rD, rs1, rs2". rs2[4:0] defines the location of the LSB
#that is extracted, while rs2[9:5] defines the number of bits that are extracted. answer is sign extended
#based upon the MSB of the extracted value rD = Zext((rs1 & ((1 << (rs2[9:5] + 1)) -1) << rs2[4:0]) >> rs2[4:0]), (rs2[9:5]+rs2[4:0])<=32
test13: #equivalent of p.extract x18, x20, 11, 3
    li x20, 0x23198519
    li x21, 0x79820963
    p.extractr x18, x20, x21
    li x19, 0x0a3
    beq x18, x19, test14
    c.addi x15, 0x1
test14: #equivalent of p.extract x18, x20, 9, 18 
    li x20, 0xb6459987
    li x21, 0x28736532
    p.extractr x18, x20, x21
    li x19, 0x00000191
    beq x18, x19, test15
    c.addi x15, 0x1
test15: #equivalent of p.extract x18, x20, 8, 7
    li x20, 0x27384928
    li x21, 0x16385907
    p.extractr x18, x20, x21
    li x19, 0x092
    beq x18, x19, test16
    c.addi x15, 0x1
test16: #equivalent of p.extract x18, x20, 17, 3
    li x20, 0x56391846
    li x21, 0x37197223
    p.extractr x18, x20, x21
    li x19, 0xffff2308
    beq x18, x19, test17
    c.addi x15, 0x1
test17: #equivalent of p.extract x18, x20, 16, 3
    li x20, 0x02374920
    li x21, 0x57723603
    p.extractr x18, x20, x21
    li x19, 0x0e924
    beq x18, x19, test18
    c.addi x15, 0x1
test18: #equivalent of p.extract x18, x20, 0, 20
    li x20, 0x37592873
    li x21, 0x21829814
    p.extractr x18, x20, x21
    li x19, 0xffffffff
    beq x18, x19, test19
    c.addi x15, 0x1
    j test19
#tests19-24 test the p.extractr instruction. values loaded in and compared to are expected output values
#p.extractr instruction is of format "p.extractu rD, rs1, rs2". rs2[4:0] defines the location of the LSB
#that is extracted, while rs2[9:5] defines the number of bits that are extracted. answer is sign extended
#based upon the MSB of the extracted value rD = Zext((rs1 & ((1 << (rs2[9:5] + 1)) -1) << rs2[4:0]) >> rs2[4:0]), (rs2[9:5]+rs2[4:0])<=32
test19: #equivalent of p.extractu x18, x20, 11, 3
    li x20, 0x23198519
    li x21, 0x79820963
    p.extractur x18, x20, x21
    li x19, 0x0a3
    beq x18, x19, test20
    c.addi x15, 0x1
test20: #equivalent of p.extractu x18, x20, 9, 18 
    li x20, 0xb6459987
    li x21, 0x28736532
    p.extractur x18, x20, x21
    li x19, 0x191
    beq x18, x19, test21
    c.addi x15, 0x1
test21: #equivalent of p.extractu x18, x20, 8, 7
    li x20, 0x27384928
    li x21, 0x16385907
    p.extractur x18, x20, x21
    li x19, 0x092
    beq x18, x19, test22
    c.addi x15, 0x1
test22: #equivalent of p.extractu x18, x20, 17, 3
    li x20, 0x56391846
    li x21, 0x37197223
    p.extractur x18, x20, x21
    li x19, 0x32308
    beq x18, x19, test23
    c.addi x15, 0x1
test23: #equivalent of p.extractu x18, x20, 16, 3
    li x20, 0x02374920
    li x21, 0x57723603
    p.extractur x18, x20, x21
    li x19, 0x0e924
    beq x18, x19, test24
    c.addi x15, 0x1
test24: #equivalent of p.extractu x18, x20, 0, 20
    li x20, 0x37592873
    li x21, 0x21829814
    p.extractur x18, x20, x21
    li x19, 0x1
    beq x18, x19, test25
    c.addi x15, 0x1
    j test25
#tests25-30 test the p.insert instruction. values loaded in and compared to are expected values
#p.insert instruction is of format "p.insert rD, rs1, ls3, ls2". ls3 determines which bits [ls3:0]
#are inserted, while ls2 defines the magnitude of the left shift. All bits of rD not inserted to are passed
#through unchanged. rD = (rD & ~(rs1[ls3:0]<<ls2))|(rs1[ls3:0]<<ls2), (ls3+ls2)<=32
test25:
    li x18, 0xffffffff
    li x20, 0x12577823
    p.insert x18, x20, 8, 24
    li x19, 0x23ffffff
    beq x18, x19, test26
    c.addi x15, 0x1
test26:
    li x18, 0x00000000
    li x20, 0x85763245
    p.insert x18, x20, 1, 31
    li x19, 0x80000000
    beq x18, x19, test27
    c.addi x15, 0x1
test27:
    li x18, 0xffffffff
    li x20, 0x69879573
    p.insert x18, x20, 8, 0
    li x19, 0xffffff73
    beq x18, x19, test28
    c.addi x15, 0x1
test28:
    li x18, 0x00000000
    li x20, 0x12577823
    p.insert x18, x20, 1, 0
    li x19, 0x3
    beq x18, x19, test29
    c.addi x15, 0x1
test29:
    li x18, 0xffffffff
    li x20, 0x34667485
    p.insert x18, x20, 7, 16
    li x19, 0xff85ffff
    beq x18, x19, test30
    c.addi x15, 0x1
test30:
    li x18, 0x00000000
    li x20, 0x78729209
    p.insert x18, x20, 16, 2
    li x19, 0x24824
    beq x18, x19, test31
    c.addi x15, 0x1
    j test31
#tests31-36 test the p.insertr instruction. values loaded in and compared to are expected values
#p.insertr instruction is of format "p.insertr rD, rs1, rs2". rs2[9:5] determines which bits [rs2[9:5]:0]
#are inserted, while rs2[4:0] defines the magnitude of the left shift. All bits of rD not inserted to are passed
#through unchanged. rD = (rD & ~(rs1[rs2[9:5]:0]<<ls2))|(rs1[rs2[9:5]:0]<<rs2[4:0]), (rs2[9:5]+rs2[4:0])<=32
test31:
    li x18, 0xffffffff
    li x20, 0x37492846
    li x21, 0x01927326
    p.insertr x18, x20, x21
    li x19, 0xd24a11bf
    beq x18, x19, test32
    c.addi x15, 0x1
test32:
    li x18, 0x00000000
    li x20, 0x11049275
    li x21, 0x27402831
    p.insertr x18, x20, x21
    li x19, 0x00020000
    beq x18, x19, test33
    c.addi x15, 0x1
test33:
    li x18, 0xffffffff
    li x20, 0x27493857
    li x21, 0x28039740
    p.insertr x18, x20, x21
    li x19, 0xff493857
    beq x18, x19, test34
    c.addi x15, 0x1
test34:
    li x18, 0x00000000
    li x20, 0x82068834
    li x21, 0x01926875
    p.insertr x18, x20, x21
    li x19, 0x00800000
    beq x18, x19, test35
    c.addi x15, 0x1
test35:
    li x18, 0xffffffff
    li x20, 0x28407279
    li x21, 0x34562167
    p.insertr x18, x20, x21
    li x19, 0xfff93cff
    beq x18, x19, test36
    c.addi x15, 0x1
test36:
    li x18, 0x00000000
    li x20, 0x27049709
    li x21, 0x27070193
    p.insertr x18, x20, x21
    li x19, 0xb8480000
    beq x18, x19, test37
    c.addi x15, 0x1
    j test37
#tests37-42 test the p.bclr instruction. values loaded in and compared to are expected values
#p.bclr instruction is of format "p.bclr rD, rs1, ls3, ls2". ls3 determines how many bits are cleared
#while ls2 determines the left shift of the cleared bit range. All bits of rs1 not cleared are passed
#through unchanged. rD = rs1 & ~(((1 << (ls3+1)) - 1) << ls2), (ls3+ls2) <= 32
test37:
    li x20, 0x12577823
    p.bclr x18, x20, 8, 24
    li x19, 0x00577823
    beq x18, x19, test38
    c.addi x15, 0x1
test38:
    li x20, 0x85763245
    p.bclr x18, x20, 1, 31
    li x19, 0x05763245
    beq x18, x19, test39
    c.addi x15, 0x1
test39:
    li x20, 0x69879573
    p.bclr x18, x20, 8, 0
    li x19, 0x69879400
    beq x18, x19, test40
    c.addi x15, 0x1
test40:
    li x20, 0x12577823
    p.bclr x18, x20, 1, 0
    li x19, 0x12577820
    beq x18, x19, test41
    c.addi x15, 0x1
test41:
    li x20, 0x34667485
    p.bclr x18, x20, 7, 16
    li x19, 0x34007485
    beq x18, x19, test42
    c.addi x15, 0x1
test42:
    li x20, 0x78729209
    p.bclr x18, x20, 16, 2
    li x19, 0x78700001
    beq x18, x19, test43
    c.addi x15, 0x1
    j test43
#tests43-48 test the p.bclrr instruction. values loaded in and compared to are expected values
#p.bclrr instruction is of format "p.bclrr rD, rs1, rs2". rs2[9:5] determines how many bits are cleared
#while rs2[4:0] determines the left shift of the cleared bit range. All bits of rs1 not cleared are passed
#through unchanged. rD = rs1 & ~(((1 << (rs2[9:5]+1)) - 1) << rs2[4:0]), (rs2[9:5]+rs2[4:0]) <= 32
test43:
    li x20, 0x37492846
    li x21, 0x01927326
    p.bclrr x18, x20, x21
    li x19, 0x00000006
    beq x18, x19, test44
    c.addi x15, 0x1
test44:
    li x20, 0x11049275
    li x21, 0x27402831
    p.bclrr x18, x20, x21
    li x19, 0x11009275
    beq x18, x19, test45
    c.addi x15, 0x1
test45:
    li x20, 0x27493857
    li x21, 0x28039740
    p.bclrr x18, x20, x21
    li x19, 0x20000000
    beq x18, x19, test46
    c.addi x15, 0x1
test46:
    li x20, 0x82068834
    li x21, 0x01926875
    p.bclrr x18, x20, x21
    li x19, 0x82068834
    beq x18, x19, test47
    c.addi x15, 0x1
test47:
    li x20, 0x28407279
    li x21, 0x34562167
    p.bclrr x18, x20, x21
    li x19, 0x28400079
    beq x18, x19, test48
    c.addi x15, 0x1
test48:
    li x20, 0x27049709
    li x21, 0x27070193
    p.bclrr x18, x20, x21
    li x19, 0x00049709
    beq x18, x19, test49
    c.addi x15, 0x1
    j test49
#tests49-54 test the p.bset instruction. values loaded in and compared to are expected values
#p.bset instruction is of format "p.bset rD, rs1, ls3, ls2". ls3 determines how many bits are set
#while ls2 determines the left shift of the set bit range. All bits of rs1 not set are passed
#through unchanged. rD = rs1 | (((1 << (ls3+1)) - 1) << ls2), (ls3+ls2) <= 32
test49:
    li x20, 0x12577823
    p.bset x18, x20, 8, 24
    li x19, 0xff577823
    beq x18, x19, test50
    c.addi x15, 0x1
test50:
    li x20, 0x85763245
    p.bset x18, x20, 1, 31
    li x19, 0x85763245
    beq x18, x19, test51
    c.addi x15, 0x1
test51:
    li x20, 0x69879573
    p.bset x18, x20, 8, 0
    li x19, 0x698795ff
    beq x18, x19, test52
    c.addi x15, 0x1
test52:
    li x20, 0x12577823
    p.bset x18, x20, 1, 0
    li x19, 0x12577823
    beq x18, x19, test53
    c.addi x15, 0x1
test53:
    li x20, 0x34667485
    p.bset x18, x20, 7, 16
    li x19, 0x34ff7485
    beq x18, x19, test54
    c.addi x15, 0x1
test54:
    li x20, 0x78729209
    p.bset x18, x20, 16, 2
    li x19, 0x7877fffd
    beq x18, x19, test55
    c.addi x15, 0x1
    j test55
#tests55-60 test the p.bsetr instruction. values loaded in and compared to are expected values
#p.bsetr instruction is of format "p.bsetr rD, rs1, rs2". rs2[9:5] determines how many bits are set
#while rs2[4:0] determines the left shift of the set bit range. All bits of rs1 not set are passed
#through unchanged. rD = rs1 | (((1 << (rs2[9:5]+1)) - 1) << rs2[4:0]), (rs2[9:5]+rs2[4:0]) <= 32
test55:
    li x20, 0x37492846
    li x21, 0x01927326
    p.bsetr x18, x20, x21
    li x19, 0xffffffc6
    beq x18, x19, test56
    c.addi x15, 0x1
test56:
    li x20, 0x11049275
    li x21, 0x27402831
    p.bsetr x18, x20, x21
    li x19, 0x11069275
    beq x18, x19, test57
    c.addi x15, 0x1
test57:
    li x20, 0x27493857
    li x21, 0x28039740
    p.bsetr x18, x20, x21
    li x19, 0x27ffffff
    beq x18, x19, test58
    c.addi x15, 0x1
test58:
    li x20, 0x82068834
    li x21, 0x01926875
    p.bsetr x18, x20, x21
    li x19, 0x83e68834
    beq x18, x19, test59
    c.addi x15, 0x1
test59:
    li x20, 0x28407279
    li x21, 0x34562167
    p.bsetr x18, x20, x21
    li x19, 0x2847fff9
    beq x18, x19, test60
    c.addi x15, 0x1
test60:
    li x20, 0x27049709
    li x21, 0x27070193
    p.bsetr x18, x20, x21
    li x19, 0xfffc9709
    beq x18, x19, test61
    c.addi x15, 0x1
    j test61
#tests61-66 test the p.ff1 instruction. values loaded in and compared to are expected values
#p.ff1 instruction is of format "p.ff1 rD, rs1". rD is set to the value of the bit of rs1 with
#least signifigance that is set. If no bits are set, rD is set to 32
test61:
    li x20, 0x00000000
    p.ff1 x19, x20
    li x18, 0x20
    beq x18, x19, test62
    c.addi x15, 0x1
test62:
    li x20, 0xffffffff
    p.ff1 x19, x20
    li x18, 0x0
    beq x18, x19, test63
    c.addi x15, 0x1
test63:
    li x20, 0x00000001
    p.ff1 x19, x20
    li x18, 0x0
    beq x18, x19, test64
    c.addi x15, 0x1
test64:
    li x20, 0x80000000
    p.ff1 x19, x20
    li x18, 0x1f
    beq x18, x19, test65
    c.addi x15, 0x1
test65:
    li x20, 0x00455400
    p.ff1 x19, x20
    li x18, 0xa
    beq x18, x19, test66
    c.addi x15, 0x1
test66:
    li x20, 0x00022000
    p.ff1 x19, x20
    li x18, 0xd
    beq x18, x19, test67
    c.addi x15, 0x1
#tests67-72 test the p.fl1 instruction. values loaded in and compared to are expected values
#p.fl1 instruction is of format "p.fl1 rD, rs1". rD is set to the value of the last bit of rs1
#that is set starting from MSB
test67:
    li x20, 0x00000000
    p.fl1 x19, x20
    li x18, 0x20
    beq x18, x19, test68
    c.addi x15, 0x1
test68:
    li x20, 0xffffffff
    p.fl1 x19, x20
    li x18, 0x1f
    beq x18, x19, test69
    c.addi x15, 0x1
test69:
    li x20, 0x00000001
    p.fl1 x19, x20
    li x18, 0x0
    beq x18, x19, test70
    c.addi x15, 0x1
test70:
    li x20, 0x80000000
    p.fl1 x19, x20
    li x18, 0x1f
    beq x18, x19, test71
    c.addi x15, 0x1
test71:
    li x20, 0x00455400
    p.fl1 x19, x20
    li x18, 0x16
    beq x18, x19, test72
    c.addi x15, 0x1
test72:
    li x20, 0x00022000
    p.fl1 x19, x20
    li x18, 0x11
    beq x18, x19, test73
    c.addi x15, 0x1
#tests 73-78 test the p.clb instruction. values loaded in and compared to are expected values
#p.clb instruction is of format "p.clb rD, rs1". rD is set to the value of the total of leading
#bits that match (length of starting string of 1's or 0's starting from MSB). If rs1=0, then rD=0
test73:
    li x20, 0x00000000
    p.clb x19, x20
    li x18, 0x0
    beq x18, x19, test74
    c.addi x15, 0x1
test74:
    li x20, 0xffffffff
    p.clb x19, x20
    li x18, 0x1f
    beq x18, x19, test75
    c.addi x15, 0x1
test75:
    li x20, 0x90723073
    p.clb x19, x20
    li x18, 0x0
    beq x18, x19, test76
    c.addi x15, 0x1
test76:
    li x20, 0xff092736
    p.clb x19, x20
    li x18, 0x7
    beq x18, x19, test77
    c.addi x15, 0x1
test77:
    li x20, 0x00455400
    p.clb x19, x20
    li x18, 0x8
    beq x18, x19, test78
    c.addi x15, 0x1
test78:
    li x20, 0x00009276
    p.clb x19, x20
    li x18, 0xf
    beq x18, x19, test79
    c.addi x15, 0x1
#tests 79-84 test the p.cnt instruction. values loaded in and compared to are expected values
#p.cnt instruction is of format "p.clb rD, rs1". rD is set to the population of rs1, wherein the
#population is defined as the number of bits that are set in rs1
test79:
    li x20, 0x00000000
    p.cnt x19, x20
    li x18, 0x0
    beq x18, x19, test80
    c.addi x15, 0x1
test80:
    li x20, 0xffffffff
    p.cnt x19, x20
    li x18, 0x20
    beq x18, x19, test81
    c.addi x15, 0x1
test81:
    li x20, 0x90723073
    p.cnt x19, x20
    li x18, 0xd
    beq x18, x19, test82
    c.addi x15, 0x1
test82:
    li x20, 0xff092736
    p.cnt x19, x20
    li x18, 0x12
    beq x18, x19, test83
    c.addi x15, 0x1
test83:
    li x20, 0x00455400
    p.cnt x19, x20
    li x18, 0x6
    beq x18, x19, test84
    c.addi x15, 0x1
test84:
    li x20, 0x00009276
    p.cnt x19, x20
    li x18, 0x8
    beq x18, x19, test85
    c.addi x15, 0x1
#tests 85-90 test the p.ror instruction. values loaded in and compared to are expected values
#p.ror instruction is of format "p.ror rD, rs1, rs2". rD is set to the value of rs1 rotated right
#by the value defined in rs2
test85:
    li x20, 0x00000000
    li x21, 0x09450702
    p.ror x19, x20, x21
    li x18, 0x0
    beq x18, x19, test86
    c.addi x15, 0x1
test86:
    li x20, 0xffffffff
    li x21, 0x70923608
    p.ror x19, x20, x21
    li x18, 0xffffffff
    beq x18, x19, test87
    c.addi x15, 0x1
test87:
    li x20, 0x0f0f0f0f
    li x21, 0x00000004
    p.ror x19, x20, x21
    li x18, 0xf0f0f0f0
    beq x18, x19, test88
    c.addi x15, 0x1
test88:
    li x20, 0x0000ffff
    li x21, 0x00000010
    p.ror x19, x20, x21
    li x18, 0xffff0000
    beq x18, x19, test89
    c.addi x15, 0x1
test89:
    li x20, 0xa5a5a5a5
    li x21, 0x00000001
    p.ror x19, x20, x21
    li x18, 0xd2d2d2d2
    beq x18, x19, test90
    c.addi x15, 0x1
test90:
    li x20, 0x5a5a5a5a
    li x21, 0x00000001
    p.ror x19, x20, x21
    li x18, 0x2d2d2d2d
    beq x18, x19, test91
    c.addi x15, 0x1
#tests91-96 test the p.bitrev instruction. values loaded in and compared to are expected values
#p.bitrev instruction is of format "p.bitrev rD, rs1, ls3, ls2". returns a bit reversed representation
#assuming a FFT with input rs1 on 2^ls2 points in radix 2^ls3 where ls3 is 1, 2, or 3.
test91:
    li x20, 0x32f0edf4
    .word 0xc44a5933    #p.bitrev x18, x20, 4, 2
    li x19, 0x02edf199
    beq x18, x19, test92
    c.addi x15, 0x1
test92:
    li x20, 0x44f4c26f
    .word 0xc26a5933    #p.bitrev x18, x20, 6, 1
    li x19, 0x03e60c7c
    beq x18, x19, test93
    c.addi x15, 0x1
test93:
    li x20, 0x7e6b77d4
    .word 0xc07a5933    #p.bitrev x18, x20, 7, 0
    li x19, 0x0057ddac
    beq x18, x19, test94
    c.addi x15, 0x1
test94:
    li x20, 0x44261e8e
    .word 0xc43a5933    #p.bitrev x18, x20, 3, 2
    li x19, 0x23998681
    beq x18, x19, test95
    c.addi x15, 0x1
test95:
    li x20, 0x015b4f09
    .word 0xc20a5933    #p.bitrev x18, x20, 0, 1
    li x19, 0x60f1e540
    beq x18, x19, test96
    c.addi x15, 0x1
test96:
    li x20, 0xf5f7164d
    .word 0xc02a5933    #p.bitrev x18, x20, 2, 0
    li x19, 0x2c9a3beb
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
