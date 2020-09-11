.globl _start
.globl main
.globl exit
.section .text
.global test_results
test_results:
	.word 123456789
#tests all post-increment load/store instructions. NOTE: value of register x15 at the end of the test is the error count
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
#tests1-6 test the p.lb instruction (immediate offset). values loaded in and compared to are expected output values
#p.lb instruction is of format "p.lb rD, Imm(rs1!)". rD is loaded with the sign extended value at Mem8(rs1), then
#rs1 is incremented by the value of Imm. Imm has a max size of 12 bits
    li x20, 0x00120000
    li x21, 0x00120000
test1:
    li x17, 0x7c64e787
    sw x17, 0(x20)
    p.lb x18, 0x8(x20!)
    li x19, 0xffffff87
    beq x18, x19, check1
    c.addi x15, 0x1
check1:
    addi x21, x21, 0x8
    beq x20, x21, test2
    c.addi x16, 0x1
test2:
    li x17, 0xe4ea7b58
    sw x17, 0(x20)
    p.lb x18, 0x5(x20!)
    li x19, 0x00000058
    beq x18, x19, check2
    c.addi x15, 0x1
check2:
    addi x21, x21, 0x5
    beq x20, x21, test3
    c.addi x16, 0x1
test3:
    li x17, 0x366ff377
    sw x17, 0(x20)
    p.lb x18, 0xd(x20!)
    li x19, 0x00000077
    beq x18, x19, check3
    c.addi x15, 0x1
check3:
    addi x21, x21, 0xd
    beq x20, x21, test4
    c.addi x16, 0x1
test4:
    li x17, 0x17c7fa9d
    sw x17, 0(x20)
    p.lb x18, 0xbc(x20!)
    li x19, 0xffffff9d
    beq x18, x19, check4
    c.addi x15, 0x1
check4:
    addi x21, x21, 0xbc
    beq x20, x21, test5
    c.addi x16, 0x1
test5:
    li x17, 0x1b450b7b
    sw x17, 0(x20)
    p.lb x18, 0x642(x20!)
    li x19, 0x0000007b
    beq x18, x19, check5
    c.addi x15, 0x1
check5:
    addi x21, x21, 0x642
    beq x20, x21, test6
    c.addi x16, 0x1
test6:
    li x17, 0x1b2f8686
    sw x17, 0(x20)
    p.lb x18, 0x4c(x20!)
    li x19, 0xffffff86
    beq x18, x19, check6
    c.addi x15, 0x1
check6:
    addi x21, x21, 0x4c
    beq x20, x21, test7
    c.addi x16, 0x1
#tests7-12 test the p.lbu instruction (immediate offset). values loaded in and compared to are expected output values
#p.lbu instruction is of format "p.lbu rD, Imm(rs1!)". rD is loaded with the Z extended value at Mem8(rs1), then
#rs1 is incremented by the value of Imm. Imm has a max size of 12 bits
test7:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x284def7c
    sw x17, 0(x20)
    nop
    p.lbu x18, 0xa8(x20!)
    li x19, 0x00007c
    beq x18, x19, check7
    c.addi x15, 0x1
check7:
    addi x21, x21, 0xa8
    beq x20, x21, test8
    c.addi x16, 0x1
test8:
    li x17, 0x1c133aa7
    sw x17, 0(x20)
    p.lbu x18, 0x776(x20!)
    li x19, 0x000000a7
    beq x18, x19, check8
    c.addi x15, 0x1
check8:
    addi x21, x21, 0x776
    beq x20, x21, test9
    c.addi x16, 0x1
test9:
    li x17, 0xc30dc4ae
    sw x17, 0(x20)
    p.lbu x18, 0xb4(x20!)
    li x19, 0x000000ae
    beq x18, x19, check9
    c.addi x15, 0x1
check9:
    addi x21, x21, 0xb4
    beq x20, x21, test10
    c.addi x16, 0x1
test10:
    li x17, 0xd58dcbf8
    sw x17, 0(x20)
    p.lbu x18, 0x12(x20!)
    li x19, 0x000000f8
    beq x18, x19, check10
    c.addi x15, 0x1
check10:
    addi x21, x21, 0x12
    beq x20, x21, test11
    c.addi x16, 0x1
test11:
    li x17, 0x0a326929
    sw x17, 0(x20)
    p.lbu x18, 0x40(x20!)
    li x19, 0x00000029
    beq x18, x19, check11
    c.addi x15, 0x1
check11:
    addi x21, x21, 0x40
    beq x20, x21, test12
    c.addi x16, 0x1
test12:
    li x17, 0xaa36097f
    sw x17, 0(x20)
    p.lbu x18, 0x52(x20!)
    li x19, 0x0000007f
    beq x18, x19, check12
    c.addi x15, 0x1
check12:
    addi x21, x21, 0x52
    beq x20, x21, test13
    c.addi x16, 0x1
#tests13-18 test the p.lh instruction (immediate offset). values loaded in and compared to are expected output values
#p.lh instruction is of format "p.lh rD, Imm(rs1!)". rD is loaded with the sign extended value at Mem16(rs1), then
#rs1 is incremented by the value of Imm. Imm has a max size of 12 bits
test13:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x0eb518be
    sw x17, 0(x20)
    p.lh x18, 0xc8(x20!)
    li x19, 0x000018be
    beq x18, x19, check13
    c.addi x15, 0x1
check13:
    addi x21, x21, 0xc8
    beq x20, x21, test14
    c.addi x16, 0x1
test14:
    li x17, 0xae82beec
    sw x17, 0(x20)
    p.lh x18, 0x224(x20!)
    li x19, 0xffffbeec
    beq x18, x19, check14
    c.addi x15, 0x1
check14:
    addi x21, x21, 0x224
    beq x20, x21, test15
    c.addi x16, 0x1
test15:
    li x17, 0x872ff921
    sw x17, 0(x20)
    p.lh x18, 0xe0(x20!)
    li x19, 0xfffff921
    beq x18, x19, check15
    c.addi x15, 0x1
check15:
    addi x21, x21, 0xe0
    beq x20, x21, test16
    c.addi x16, 0x1
test16:
    li x17, 0x6af22644
    sw x17, 0(x20)
    p.lh x18, 0x424(x20!)
    li x19, 0x00002644
    beq x18, x19, check16
    c.addi x15, 0x1
check16:
    addi x21, x21, 0x424
    beq x20, x21, test17
    c.addi x16, 0x1
test17:
    li x17, 0xaab13adb
    sw x17, 0(x20)
    p.lh x18, 0x86(x20!)
    li x19, 0x00003adb
    beq x18, x19, check17
    c.addi x15, 0x1
check17:
    addi x21, x21, 0x86
    beq x20, x21, test18
    c.addi x16, 0x1
test18:
    li x17, 0x5a5a1ece
    sw x17, 0(x20)
    p.lh x18, 0x6fc(x20!)
    li x19, 0x00001ece
    beq x18, x19, check18
    c.addi x15, 0x1
check18:
    addi x21, x21, 0x6fc
    beq x20, x21, test19
    c.addi x16, 0x1
#tests19-24 test the p.lhu instruction (immediate offset). values loaded in and compared to are expected output values
#p.lhu instruction is of format "p.lhu rD, Imm(rs1!)". rD is loaded with the Z extended value at Mem16(rs1), then
#rs1 is incremented by the value of Imm. Imm has a max size of 12 bits
test19:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x1e9afd85
    sw x17, 0(x20)
    nop
    p.lhu x18, 0x482(x20!)
    li x19, 0x0000fd85
    beq x18, x19, check19
    c.addi x15, 0x1
check19:
    addi x21, x21, 0x482
    beq x20, x21, test20
    c.addi x16, 0x1
test20:
    li x17, 0xc78ece79
    sw x17, 0(x20)
    p.lhu x18, 0xbd(x20!)
    li x19, 0x0000ce79
    beq x18, x19, check20
    c.addi x15, 0x1
check20:
    addi x21, x21, 0xbd
    beq x20, x21, test21
    c.addi x16, 0x1
test21:
    li x17, 0xeef54369
    sw x17, 0(x20)
    p.lhu x18, 0x2d2(x20!)
    li x19, 0x00004369
    beq x18, x19, check21
    c.addi x15, 0x1
check21:
    addi x21, x21, 0x2d2
    beq x20, x21, test22
    c.addi x16, 0x1
test22:
    li x17, 0xa9f93ae3
    sw x17, 0(x20)
    p.lhu x18, 0xb(x20!)
    li x19, 0x00003ae3
    beq x18, x19, check22
    c.addi x15, 0x1
check22:
    addi x21, x21, 0xb
    beq x20, x21, test23
    c.addi x16, 0x1
test23:
    li x17, 0xee24c6e4
    sw x17, 0(x20)
    p.lhu x18, 0xee(x20!)
    li x19, 0x0000c6e4
    beq x18, x19, check23
    c.addi x15, 0x1
check23:
    addi x21, x21, 0xee
    beq x20, x21, test24
    c.addi x16, 0x1
test24:
    li x17, 0xdd8f738b
    sw x17, 0(x20)
    p.lhu x18, 0x3(x20!)
    li x19, 0x0000738b
    beq x18, x19, check24
    c.addi x15, 0x1
check24:
    addi x21, x21, 0x3
    beq x20, x21, test25
    c.addi x16, 0x1
#tests25-30 test the p.lw instruction (immediate offset). values loaded in and compared to are expected output values
#p.lw instruction is of format "p.lw rD, Imm(rs1!)". rD is loaded with the value at Mem(rs1), then
#rs1 is incremented by the value of Imm. Imm has a max size of 12 bits
test25:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0xbe54b277
    sw x17, 0(x20)
    nop
    p.lw x18, 0x5(x20!)
    li x19, 0xbe54b277
    beq x18, x19, check25
    c.addi x15, 0x1
check25:
    addi x21, x21, 0x5
    beq x20, x21, test26
    c.addi x16, 0x1
test26:
    li x17, 0xdef7980c
    sw x17, 0(x20)
    p.lw x18, 0x5cf(x20!)
    li x19, 0xdef7980c
    beq x18, x19, check26
    c.addi x15, 0x1
check26:
    addi x21, x21, 0x5cf
    beq x20, x21, test27
    c.addi x16, 0x1
test27:
    li x17, 0x1021f6d2
    sw x17, 0(x20)
    p.lw x18, 0x133(x20!)
    li x19, 0x1021f6d2
    beq x18, x19, check27
    c.addi x15, 0x1
check27:
    addi x21, x21, 0x133
    beq x20, x21, test28
    c.addi x16, 0x1
test28:
    li x17, 0x683e7019
    sw x17, 0(x20)
    p.lw x18, 0xf8(x20!)
    li x19, 0x683e7019
    beq x18, x19, check28
    c.addi x15, 0x1
check28:
    addi x21, x21, 0xf8
    beq x20, x21, test29
    c.addi x16, 0x1
test29:
    li x17, 0xe4f76ef9
    sw x17, 0(x20)
    p.lw x18, 0x6(x20!)
    li x19, 0xe4f76ef9
    beq x18, x19, check29
    c.addi x15, 0x1
check29:
    addi x21, x21, 0x6
    beq x20, x21, test30
    c.addi x16, 0x1
test30:
    li x17, 0xd1337559
    sw x17, 0(x20)
    p.lw x18, 0xd5(x20!)
    li x19, 0xd1337559
    beq x18, x19, check30
    c.addi x15, 0x1
check30:
    addi x21, x21, 0xd5
    beq x20, x21, test31
    c.addi x16, 0x1
#tests31-36 test the p.lb instruction (register offset). values loaded in and compared to are expected output values
#p.lb instruction is of format "p.lb rD, rs2(rs1!)". rD is loaded with the sign extended value at Mem8(rs1), then
#rs1 is incremented by the value of rs2
test31:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x7c64e787
    li x22, 0x8
    sw x17, 0(x20)
    p.lb x18, x22(x20!)
    li x19, 0xffffff87
    beq x18, x19, check31
    c.addi x15, 0x1
check31:
    addi x21, x21, 0x8
    beq x20, x21, test32
    c.addi x16, 0x1
test32:
    li x17, 0xe4ea7b58
    li x22, 0x5
    sw x17, 0(x20)
    p.lb x18, x22(x20!)
    li x19, 0x00000058
    beq x18, x19, check32
    c.addi x15, 0x1
check32:
    addi x21, x21, 0x5
    beq x20, x21, test33
    c.addi x16, 0x1
test33:
    li x17, 0x366ff377
    li x22, 0xd
    sw x17, 0(x20)
    p.lb x18, x22(x20!)
    li x19, 0x00000077
    beq x18, x19, check33
    c.addi x15, 0x1
check33:
    addi x21, x21, 0xd
    beq x20, x21, test34
    c.addi x16, 0x1
test34:
    li x17, 0x17c7fa9d
    li x22, 0xbc
    sw x17, 0(x20)
    p.lb x18, x22(x20!)
    li x19, 0xffffff9d
    beq x18, x19, check34
    c.addi x15, 0x1
check34:
    addi x21, x21, 0xbc
    beq x20, x21, test35
    c.addi x16, 0x1
test35:
    li x17, 0x1b450b7b
    li x22, 0x642
    sw x17, 0(x20)
    p.lb x18, x22(x20!)
    li x19, 0x0000007b
    beq x18, x19, check35
    c.addi x15, 0x1
check35:
    addi x21, x21, 0x642
    beq x20, x21, test36
    c.addi x16, 0x1
test36:
    li x17, 0x1b2f8686
    li x22, 0x4c
    sw x17, 0(x20)
    p.lb x18, x22(x20!)
    li x19, 0xffffff86
    beq x18, x19, check36
    c.addi x15, 0x1
check36:
    addi x21, x21, 0x4c
    beq x20, x21, test37
    c.addi x16, 0x1
#tests37-42 test the p.lbu instruction (register offset). values loaded in and compared to are expected output values
#p.lbu instruction is of format "p.lbu rD, rs2(rs1!)". rD is loaded with the Z extended value at Mem8(rs1), then
#rs1 is incremented by the value of rs2.
test37:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x284def7c
    li x22, 0xa8
    sw x17, 0(x20)
    nop
    p.lbu x18, x22(x20!)
    li x19, 0x00007c
    beq x18, x19, check37
    c.addi x15, 0x1
check37:
    addi x21, x21, 0xa8
    beq x20, x21, test38
    c.addi x16, 0x1
test38:
    li x17, 0x1c133aa7
    li x22, 0x776
    sw x17, 0(x20)
    p.lbu x18, x22(x20!)
    li x19, 0x000000a7
    beq x18, x19, check38
    c.addi x15, 0x1
check38:
    addi x21, x21, 0x776
    beq x20, x21, test39
    c.addi x16, 0x1
test39:
    li x17, 0xc30dc4ae
    li x22, 0xb4
    sw x17, 0(x20)
    p.lbu x18,x22(x20!)
    li x19, 0x000000ae
    beq x18, x19, check39
    c.addi x15, 0x1
check39:
    addi x21, x21, 0xb4
    beq x20, x21, test40
    c.addi x16, 0x1
test40:
    li x17, 0xd58dcbf8
    li x22, 0x12
    sw x17, 0(x20)
    p.lbu x18, x22(x20!)
    li x19, 0x000000f8
    beq x18, x19, check40
    c.addi x15, 0x1
check40:
    addi x21, x21, 0x12
    beq x20, x21, test41
    c.addi x16, 0x1
test41:
    li x17, 0x0a326929
    li x22, 0x40
    sw x17, 0(x20)
    p.lbu x18, x22(x20!)
    li x19, 0x00000029
    beq x18, x19, check41
    c.addi x15, 0x1
check41:
    addi x21, x21, 0x40
    beq x20, x21, test42
    c.addi x16, 0x1
test42:
    li x17, 0xaa36097f
    li x22, 0x52
    sw x17, 0(x20)
    p.lbu x18, x22(x20!)
    li x19, 0x0000007f
    beq x18, x19, check42
    c.addi x15, 0x1
check42:
    addi x21, x21, 0x52
    beq x20, x21, test43
    c.addi x16, 0x1
#tests43-48 test the p.lh instruction (register offset). values loaded in and compared to are expected output values
#p.lh instruction is of format "p.lh rD, rs2(rs1!)". rD is loaded with the sign extended value at Mem16(rs1), then
#rs1 is incremented by the value of rs2.
test43:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x0eb518be
    li x22, 0xc8
    sw x17, 0(x20)
    p.lh x18, x22(x20!)
    li x19, 0x000018be
    beq x18, x19, check43
    c.addi x15, 0x1
check43:
    addi x21, x21, 0xc8
    beq x20, x21, test44
    c.addi x16, 0x1
test44:
    li x17, 0xae82beec
    li x22, 0x224
    sw x17, 0(x20)
    p.lh x18, x22(x20!)
    li x19, 0xffffbeec
    beq x18, x19, check44
    c.addi x15, 0x1
check44:
    addi x21, x21, 0x224
    beq x20, x21, test45
    c.addi x16, 0x1
test45:
    li x17, 0x872ff921
    li x22, 0xe0
    sw x17, 0(x20)
    p.lh x18, x22(x20!)
    li x19, 0xfffff921
    beq x18, x19, check45
    c.addi x15, 0x1
check45:
    addi x21, x21, 0xe0
    beq x20, x21, test46
    c.addi x16, 0x1
test46:
    li x17, 0x6af22644
    li x22, 0x424
    sw x17, 0(x20)
    p.lh x18, x22(x20!)
    li x19, 0x00002644
    beq x18, x19, check46
    c.addi x15, 0x1
check46:
    addi x21, x21, 0x424
    beq x20, x21, test47
    c.addi x16, 0x1
test47:
    li x17, 0xaab13adb
    li x22, 0x86
    sw x17, 0(x20)
    p.lh x18, x22(x20!)
    li x19, 0x00003adb
    beq x18, x19, check47
    c.addi x15, 0x1
check47:
    addi x21, x21, 0x86
    beq x20, x21, test48
    c.addi x16, 0x1
test48:
    li x17, 0x5a5a1ece
    li x22, 0x6fc
    sw x17, 0(x20)
    p.lh x18, x22(x20!)
    li x19, 0x00001ece
    beq x18, x19, check48
    c.addi x15, 0x1
check48:
    addi x21, x21, 0x6fc
    beq x20, x21, test49
    c.addi x16, 0x1
#tests49-54 test the p.lhu instruction (register offset). values loaded in and compared to are expected output values
#p.lhu instruction is of format "p.lhu rD, rs2(rs1!)". rD is loaded with the Z extended value at Mem16(rs1), then
#rs1 is incremented by the value of rs2.
test49:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x1e9afd85
    li x22, 0x482
    sw x17, 0(x20)
    nop
    p.lhu x18, x22(x20!)
    li x19, 0x0000fd85
    beq x18, x19, check49
    c.addi x15, 0x1
check49:
    addi x21, x21, 0x482
    beq x20, x21, test50
    c.addi x16, 0x1
test50:
    li x17, 0xc78ece79
    li x22, 0xbd
    sw x17, 0(x20)
    p.lhu x18, x22(x20!)
    li x19, 0x0000ce79
    beq x18, x19, check50
    c.addi x15, 0x1
check50:
    addi x21, x21, 0xbd
    beq x20, x21, test51
    c.addi x16, 0x1
test51:
    li x17, 0xeef54369
    li x22, 0x2d2
    sw x17, 0(x20)
    p.lhu x18, x22(x20!)
    li x19, 0x00004369
    beq x18, x19, check51
    c.addi x15, 0x1
check51:
    addi x21, x21, 0x2d2
    beq x20, x21, test52
    c.addi x16, 0x1
test52:
    li x17, 0xa9f93ae3
    li x22, 0xb
    sw x17, 0(x20)
    p.lhu x18, x22(x20!)
    li x19, 0x00003ae3
    beq x18, x19, check52
    c.addi x15, 0x1
check52:
    addi x21, x21, 0xb
    beq x20, x21, test53
    c.addi x16, 0x1
test53:
    li x17, 0xee24c6e4
    li x22, 0xee
    sw x17, 0(x20)
    p.lhu x18, x22(x20!)
    li x19, 0x0000c6e4
    beq x18, x19, check53
    c.addi x15, 0x1
check53:
    addi x21, x21, 0xee
    beq x20, x21, test54
    c.addi x16, 0x1
test54:
    li x17, 0xdd8f738b
    li x22, 0x3
    sw x17, 0(x20)
    p.lhu x18, x22(x20!)
    li x19, 0x0000738b
    beq x18, x19, check54
    c.addi x15, 0x1
check54:
    addi x21, x21, 0x3
    beq x20, x21, test55
    c.addi x16, 0x1
#tests55-60 test the p.lw instruction (register offset). values loaded in and compared to are expected output values
#p.lw instruction is of format "p.lw rD, rs2(rs1!)". rD is loaded with the value at Mem(rs1), then
#rs1 is incremented by the value of rs2.
test55:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0xbe54b277
    li x22, 0x5
    sw x17, 0(x20)
    nop
    p.lw x18, x22(x20!)
    li x19, 0xbe54b277
    beq x18, x19, check55
    c.addi x15, 0x1
check55:
    addi x21, x21, 0x5
    beq x20, x21, test56
    c.addi x16, 0x1
test56:
    li x17, 0xdef7980c
    li x22, 0x5cf
    sw x17, 0(x20)
    p.lw x18, x22(x20!)
    li x19, 0xdef7980c
    beq x18, x19, check56
    c.addi x15, 0x1
check56:
    addi x21, x21, 0x5cf
    beq x20, x21, test57
    c.addi x16, 0x1
test57:
    li x17, 0x1021f6d2
    li x22, 0x133
    sw x17, 0(x20)
    p.lw x18, x22(x20!)
    li x19, 0x1021f6d2
    beq x18, x19, check57
    c.addi x15, 0x1
check57:
    addi x21, x21, 0x133
    beq x20, x21, test58
    c.addi x16, 0x1
test58:
    li x17, 0x683e7019
    li x22, 0xf8
    sw x17, 0(x20)
    p.lw x18, x22(x20!)
    li x19, 0x683e7019
    beq x18, x19, check58
    c.addi x15, 0x1
check58:
    addi x21, x21, 0xf8
    beq x20, x21, test59
    c.addi x16, 0x1
test59:
    li x17, 0xe4f76ef9
    li x22, 0x6
    sw x17, 0(x20)
    p.lw x18, x22(x20!)
    li x19, 0xe4f76ef9
    beq x18, x19, check59
    c.addi x15, 0x1
check59:
    addi x21, x21, 0x6
    beq x20, x21, test60
    c.addi x16, 0x1
test60:
    li x17, 0xd1337559
    li x22, 0xd5
    sw x17, 0(x20)
    p.lw x18, x22(x20!)
    li x19, 0xd1337559
    beq x18, x19, check60
    c.addi x15, 0x1
check60:
    addi x21, x21, 0xd5
    beq x20, x21, test61
    c.addi x16, 0x1
#tests61-66 test the p.lb instruction (register-register). values loaded in and compared to are expected output values
#p.lb instruction is of format "p.lb rD, rs2(rs1)". rD is loaded with the sign extended value at Mem8(rs1+rs2)
test61:
    li x20, 0x00120000
    li x21, 0x00000989
    li x17, 0xd926073a
    add x22, x21, x20
    sw x17, 0(x22)
    p.lb x18, x21(x20)
    li x19, 0x0000003a
    beq x18, x19, test62
    c.addi x15, 0x1
test62:
    li x21, 0x0000b58b
    li x17, 0xa3a9a146
    add x22, x21, x20
    sw x17, 0(x22)
    p.lb x18, x21(x20)
    li x19, 0x00000046
    beq x18, x19, test63
    c.addi x15, 0x1
test63:
    li x21, 0x00008381
    li x17, 0xeeeba2f8
    add x22, x21, x20
    sw x17, 0(x22)
    p.lb x18, x21(x20)
    li x19, 0xfffffff8
    beq x18, x19, test64
    c.addi x15, 0x1
test64:
    li x21, 0x00004264
    li x17, 0x1e6cd7a5
    add x22, x21, x20
    sw x17, 0(x22)
    p.lb x18, x21(x20)
    li x19, 0xffffffa5
    beq x18, x19, test65
    c.addi x15, 0x1
test65:
    li x21, 0x00000065
    li x17, 0x8b05a745
    add x22, x21, x20
    sw x17, 0(x22)
    p.lb x18, x21(x20)
    li x19, 0x00000045
    beq x18, x19, test66
    c.addi x15, 0x1
test66:
    li x21, 0x00007187
    li x17, 0x74ac19d2
    add x22, x21, x20
    sw x17, 0(x22)
    p.lb x18, x21(x20)
    li x19, 0xffffffd2
    beq x18, x19, test67
    c.addi x15, 0x1
#tests67-72 test the p.lbu instruction (register-register). values loaded in and compared to are expected output values
#p.lbu instruction is of format "p.lbu rD, rs2(rs1)". rD is loaded with the Z extended value at Mem8(rs1+rs2)
test67:
    li x20, 0x00120000
    li x21, 0x0000ee20
    li x17, 0xe4a7bad6
    add x22, x21, x20
    sw x17, 0(x22)
    p.lbu x18, x21(x20)
    li x19, 0x000000d6
    beq x18, x19, test68
    c.addi x15, 0x1
test68:
    li x21, 0x000000ae
    li x17, 0x7bacb5d3
    add x22, x21, x20
    sw x17, 0(x22)
    p.lbu x18, x21(x20)
    li x19, 0x000000d3
    beq x18, x19, test69
    c.addi x15, 0x1
test69:
    li x21, 0x000e4728
    li x17, 0x18868d88
    add x22, x21, x20
    sw x17, 0(x22)
    p.lbu x18, x21(x20)
    li x19, 0x00000088
    beq x18, x19, test70
    c.addi x15, 0x1
test70:
    li x21, 0x00000333
    li x17, 0xf72e6115
    add x22, x21, x20
    sw x17, 0(x22)
    p.lbu x18, x21(x20)
    li x19, 0x00000015
    beq x18, x19, test71
    c.addi x15, 0x1
test71:
    li x21, 0x000000cd
    li x17, 0xa8e05fa0
    add x22, x21, x20
    sw x17, 0(x22)
    p.lbu x18, x21(x20)
    li x19, 0x000000a0
    beq x18, x19, test72
    c.addi x15, 0x1
test72:
    li x21, 0x00007fee
    li x17, 0xbceff5f8
    add x22, x21, x20
    sw x17, 0(x22)
    p.lbu x18, x21(x20)
    li x19, 0x000000f8
    beq x18, x19, test73
    c.addi x15, 0x1
#tests73-78 test the p.lh instruction (register-register). values loaded in and compared to are expected output values
#p.lh instruction is of format "p.lh rD, rs2(rs1)". rD is loaded with the sign extended value at Mem16(rs1+rs2)
test73:
    li x20, 0x00120000
    li x21, 0x0000e9e7
    li x17, 0xc8d208bc
    add x22, x21, x20
    sw x17, 0(x22)
    p.lh x18, x21(x20)
    li x19, 0x000008bc
    beq x18, x19, test74
    c.addi x15, 0x1
test74:
    li x21, 0x0000084b
    li x17, 0x3388d7f6
    add x22, x21, x20
    sw x17, 0(x22)
    p.lh x18, x21(x20)
    li x19, 0xffffd7f6
    beq x18, x19, test75
    c.addi x15, 0x1
test75:
    li x21, 0x00003668
    li x17, 0x74b1bdf0
    add x22, x21, x20
    sw x17, 0(x22)
    p.lh x18, x21(x20)
    li x19, 0xffffbdf0
    beq x18, x19, test76
    c.addi x15, 0x1
test76:
    li x21, 0x00000046
    li x17, 0x3210e08f
    add x22, x21, x20
    sw x17, 0(x22)
    p.lh x18, x21(x20)
    li x19, 0xffffe08f
    beq x18, x19, test77
    c.addi x15, 0x1
test77:
    li x21, 0x0000300c
    li x17, 0x09d2f4ba
    add x22, x21, x20
    sw x17, 0(x22)
    p.lh x18, x21(x20)
    li x19, 0xfffff4ba
    beq x18, x19, test78
    c.addi x15, 0x1
test78:
    li x21, 0x0000ffc4
    li x17, 0x0da6742a
    add x22, x21, x20
    sw x17, 0(x22)
    p.lh x18, x21(x20)
    li x19, 0x0000742a
    beq x18, x19, test79
    c.addi x15, 0x1
#tests79-84 test the p.lhu instruction (register-register). values loaded in and compared to are expected output values
#p.lhu instruction is of format "p.l rD, rs2(rs1)". rD is loaded with the sign extended value at Mem16(rs1+rs2)
test79:
    li x20, 0x00120000
    li x21, 0x00002542
    li x17, 0xbabf0d25
    add x22, x21, x20
    sw x17, 0(x22)
    p.lhu x18, x21(x20)
    li x19, 0x00000d25
    beq x18, x19, test80
    c.addi x15, 0x1
test80:
    li x21, 0x00034634
    li x17, 0xb45a0335
    add x22, x21, x20
    sw x17, 0(x22)
    p.lhu x18, x21(x20)
    li x19, 0x00000335
    beq x18, x19, test81
    c.addi x15, 0x1
test81:
    li x21, 0x00000054
    li x17, 0xbff968c3
    add x22, x21, x20
    sw x17, 0(x22)
    p.lhu x18, x21(x20)
    li x19, 0x000068c3
    beq x18, x19, test82
    c.addi x15, 0x1
test82:
    li x21, 0x00000873
    li x17, 0x9e26cb44
    add x22, x21, x20
    sw x17, 0(x22)
    p.lhu x18, x21(x20)
    li x19, 0x0000cb44
    beq x18, x19, test83
    c.addi x15, 0x1
test83:
    li x21, 0x00009276
    li x17, 0xb999bf53
    add x22, x21, x20
    sw x17, 0(x22)
    p.lhu x18, x21(x20)
    li x19, 0x0000bf53
    beq x18, x19, test84
    c.addi x15, 0x1
test84:
    li x21, 0x00000003
    li x17, 0xbff9f8c3
    add x22, x21, x20
    sw x17, 0(x22)
    p.lhu x18, x21(x20)
    li x19, 0x0000f8c3
    beq x18, x19, test85
    c.addi x15, 0x1
#tests85-90 test the p.lw instruction (register-register). values loaded in and compared to are expected output values
#p.lw instruction is of format "p.lw rD, rs2(rs1)". rD is loaded with the value at Mem(rs1+rs2)
test85:
    li x20, 0x00120000
    li x21, 0x0000077d
    li x17, 0xdc23aae4
    add x22, x21, x20
    sw x17, 0(x22)
    p.lw x18, x21(x20)
    li x19, 0xdc23aae4
    beq x18, x19, test86
    c.addi x15, 0x1
test86:
    li x21, 0x000092e4
    li x17, 0x33879d8e
    add x22, x21, x20
    sw x17, 0(x22)
    p.lw x18, x21(x20)
    li x19, 0x33879d8e
    beq x18, x19, test87
    c.addi x15, 0x1
test87:
    li x21, 0x00009dc7
    li x17, 0x590e870b
    add x22, x21, x20
    sw x17, 0(x22)
    p.lw x18, x21(x20)
    li x19, 0x590e870b
    beq x18, x19, test88
    c.addi x15, 0x1
test88:
    li x21, 0x00056304
    li x17, 0xa744423e
    add x22, x21, x20
    sw x17, 0(x22)
    p.lw x18, x21(x20)
    li x19, 0xa744423e
    beq x18, x19, test89
    c.addi x15, 0x1
test89:
    li x21, 0x0000004a
    li x17, 0x34d92b34
    add x22, x21, x20
    sw x17, 0(x22)
    p.lw x18, x21(x20)
    li x19, 0x34d92b34
    beq x18, x19, test90
    c.addi x15, 0x1
test90:
    li x21, 0x00000544
    li x17, 0x99cdfd1f
    add x22, x21, x20
    sw x17, 0(x22)
    p.lw x18, x21(x20)
    li x19, 0x99cdfd1f
    beq x18, x19, test91
    c.addi x15, 0x1
#tests91-96 test the p.sb (immediate offset). values loaded in and compared to are expected output values
#p.sb instruction is of format "p.sb rs2, Imm(rs1!)". The memory location specified by rs1 is loaded with
#the lowest 8 bits of rs2, and then rs1 is post-incremented by the Imm value. Imm has a max size of 12 bits.
test91:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x45da99a1
    sw x23, 0(x20)
    p.sb x17, 0x169(x20!)
    lw x18, 0(x21)
    li x19, 0x000000a1
    beq x18, x19, check91
    c.addi x15, 0x1
check91:
    addi x21, x21, 0x169
    beq x20, x21, test92
    c.addi x16, 0x1
test92:
    li x17, 0x54cf5e63
    sw x23, 0(x20)
    p.sb x17, 0xc(x20!)
    lw x18, 0(x21)
    li x19, 0x00000063
    beq x18, x19, check92
    c.addi x15, 0x1
check92:
    addi x21, x21, 0xc
    beq x20, x21, test93
    c.addi x16, 0x1    
test93:
    li x17, 0x96ea27cf
    sw x23, 0(x20)
    p.sb x17, 0x76b(x20!)
    lw x18, 0(x21)
    li x19, 0x000000cf
    beq x18, x19, check93
    c.addi x15, 0x1
check93:
    addi x21, x21, 0x76b
    beq x20, x21, test94
    c.addi x16, 0x1
test94:
    li x17, 0xcf8223dc
    sw x23, 0(x20)
    p.sb x17, 0x43(x20!)
    lw x18, 0(x21)
    li x19, 0x000000dc
    beq x18, x19, check94
    c.addi x15, 0x1
check94:
    addi x21, x21, 0x43
    beq x20, x21, test95
    c.addi x16, 0x1
test95:
    li x17, 0x4523e08c
    sw x23, 0(x20)
    p.sb x17, 0x4e7(x20!)
    lw x18, 0(x21)
    li x19, 0x0000008c
    beq x18, x19, check95
    c.addi x15, 0x1
check95:
    addi x21, x21, 0x4e7
    beq x20, x21, test96
    c.addi x16, 0x1
test96:
    li x17, 0x2b853d75
    sw x23, 0(x20)
    p.sb x17, 0x182(x20!)
    lw x18, 0(x21)
    li x19, 0x00000075
    beq x18, x19, check96
    c.addi x15, 0x1
check96:
    addi x21, x21, 0x182
    beq x20, x21, test97
    c.addi x16, 0x1
#tests97-102 test the p.sh (immediate offset). values loaded in and compared to are expected output values
#p.sh instruction is of format "p.sh rs2, Imm(rs1!)". The memory location specified by rs1 is loaded with
#the lower 16 bits of rs2, and then rs1 is post-incremented by the Imm value. Imm has a max size of 12 bits.
test97:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x941cf440
    sw x23, 0(x20)
    p.sh x17, 0xf0(x20!)
    lw x18, 0(x21)
    li x19, 0x0000f440
    beq x18, x19, check97
    c.addi x15, 0x1
check97:
    addi x21, x21, 0xf0
    beq x20, x21, test98
    c.addi x16, 0x1
test98:
    li x17, 0xc6deecbe
    sw x23, 0(x20)
    p.sh x17, 0x2ce(x20!)
    lw x18, 0(x21)
    li x19, 0x0000ecbe
    beq x18, x19, check98
    c.addi x15, 0x1
check98:
    addi x21, x21, 0x2ce
    beq x20, x21, test99
    c.addi x16, 0x1    
test99:
    li x17, 0x2ba34fea
    sw x23, 0(x20)
    p.sh x17, 0x5c8(x20!)
    lw x18, 0(x21)
    li x19, 0x00004fea
    beq x18, x19, check99
    c.addi x15, 0x1
check99:
    addi x21, x21, 0x5c8
    beq x20, x21, test100
    c.addi x16, 0x1
test100:
    li x17, 0x6938a875
    sw x23, 0(x20)
    p.sh x17, 0x1f2(x20!)
    lw x18, 0(x21)
    li x19, 0x0000a875
    beq x18, x19, check100
    c.addi x15, 0x1
check100:
    addi x21, x21, 0x1f2
    beq x20, x21, test101
    c.addi x16, 0x1
test101:
    li x17, 0x7b72a298
    sw x23, 0(x20)
    p.sh x17, 0x19(x20!)
    lw x18, 0(x21)
    li x19, 0x0000a298
    beq x18, x19, check101
    c.addi x15, 0x1
check101:
    addi x21, x21, 0x19
    beq x20, x21, test102
    c.addi x16, 0x1
test102:
    li x17, 0x6c02d5f9
    sw x23, 0(x20)
    p.sh x17, 0xe(x20!)
    lw x18, 0(x21)
    li x19, 0x0000d5f9
    beq x18, x19, check102
    c.addi x15, 0x1
check102:
    addi x21, x21, 0xe
    beq x20, x21, test103
    c.addi x16, 0x1
#tests103-108 test the p.sw (immediate offset). values loaded in and compared to are expected output values
#p.sw instruction is of format "p.sw rs2, Imm(rs1!)". The memory location specified by rs1 is loaded with
#the value of rs2, and then rs1 is post-incremented by the Imm value. Imm has a max size of 12 bits.
test103:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0xc0020ade
    p.sw x17, 0x2d4(x20!)
    lw x18, 0(x21)
    li x19, 0xc0020ade
    beq x18, x19, check103
    c.addi x15, 0x1
check103:
    addi x21, x21, 0x2d4
    beq x20, x21, test104
    c.addi x16, 0x1
test104:
    li x17, 0x7a47d390
    p.sw x17, 0x4aa(x20!)
    lw x18, 0(x21)
    li x19, 0x7a47d390
    beq x18, x19, check104
    c.addi x15, 0x1
check104:
    addi x21, x21, 0x4aa
    beq x20, x21, test105
    c.addi x16, 0x1    
test105:
    li x17, 0x998655c1
    p.sw x17, 0x54e(x20!)
    lw x18, 0(x21)
    li x19, 0x998655c1
    beq x18, x19, check105
    c.addi x15, 0x1
check105:
    addi x21, x21, 0x54e
    beq x20, x21, test106
    c.addi x16, 0x1
test106:
    li x17, 0x4b6fe0c0
    p.sw x17, 0xa(x20!)
    lw x18, 0(x21)
    li x19, 0x4b6fe0c0
    beq x18, x19, check106
    c.addi x15, 0x1
check106:
    addi x21, x21, 0xa
    beq x20, x21, test107
    c.addi x16, 0x1
test107:
    li x17, 0xd24cd259
    p.sw x17, 0x40(x20!)
    lw x18, 0(x21)
    li x19, 0xd24cd259
    beq x18, x19, check107
    c.addi x15, 0x1
check107:
    addi x21, x21, 0x40
    beq x20, x21, test108
    c.addi x16, 0x1
test108:
    li x17, 0xb13bdb56
    p.sw x17, 0x13f(x20!)
    lw x18, 0(x21)
    li x19, 0xb13bdb56
    beq x18, x19, check108
    c.addi x15, 0x1
check108:
    addi x21, x21, 0x13f
    beq x20, x21, test109
    c.addi x16, 0x1
#tests109-114 test the p.sb (register offset). values loaded in and compared to are expected output values
#p.sb instruction is of format "p.sb rs2, rs3(rs1!)". The memory location specified by rs1 is loaded with
#the lowest 8 bits of rs2, and then rs1 is post-incremented by the value of rs3
test109:
    li x20, 0x00120000
    li x21, 0x00120000
    li x22, 0x000081ef
    li x17, 0x19726d93
    sw x23, 0(x20)
    p.sb x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x00000093
    beq x18, x19, check109
    c.addi x15, 0x1
check109:
    add x21, x21, x22
    beq x20, x21, test110
    c.addi x16, 0x1
test110:
    li x17, 0x6b186ac0
    li x22, 0x0005807
    sw x23, 0(x20)
    p.sb x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x000000c0
    beq x18, x19, check110
    c.addi x15, 0x1
check110:
    add x21, x21, x22
    beq x20, x21, test111
    c.addi x16, 0x1
test111:
    li x17, 0xdf0bcaf4
    li x22, 0x0004516d
    sw x23, 0(x20)
    p.sb x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x000000f4
    beq x18, x19, check111
    c.addi x15, 0x1
check111:
    add x21, x21, x22
    beq x20, x21, test112
    c.addi x16, 0x1
test112:
    li x17, 0x6f5f2d04
    li x22, 0x00007119
    sw x23, 0(x20)
    p.sb x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x00000004
    beq x18, x19, check112
    c.addi x15, 0x1
check112:
    add x21, x21, x22
    beq x20, x21, test113
    c.addi x16, 0x1
test113:
    li x17, 0xaa522c5c
    li x22, 0x000000d7
    sw x23, 0(x20)
    p.sb x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x0000005c
    beq x18, x19, check113
    c.addi x15, 0x1
check113:
    add x21, x21, x22
    beq x20, x21, test114
    c.addi x16, 0x1
test114:
    li x17, 0x115bc669
    li x22, 0x00000ea9
    sw x23, 0(x20)
    p.sb x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x00000069
    beq x18, x19, check114
    c.addi x15, 0x1
check114:
    add x21, x21, x22
    beq x20, x21, test115
    c.addi x16, 0x1
#tests115-120 test the p.sh (register offset). values loaded in and compared to are expected output values
#p.sh instruction is of format "p.sh rs2, rs3(rs1!)". The memory location specified by rs1 is loaded with
#the lower 16 bits of rs2, and then rs1 is post-incremented by the value of rs3
test115:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0xcd7f46b8
    li x22, 0x000001ce
    sw x23, 0(x20)
    p.sh x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x000046b8
    beq x18, x19, check115
    c.addi x15, 0x1
check115:
    add x21, x21, x22
    beq x20, x21, test116
    c.addi x16, 0x1
test116:
    li x17, 0x3469027c
    li x22, 0x00004dfe
    sw x23, 0(x20)
    p.sh x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x0000027c
    beq x18, x19, check116
    c.addi x15, 0x1
check116:
    add x21, x21, x22
    beq x20, x21, test117
    c.addi x16, 0x1    
test117:
    li x17, 0xf6e88dea
    li x22, 0x00000007
    sw x23, 0(x20)
    p.sh x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x00008dea
    beq x18, x19, check117
    c.addi x15, 0x1
check117:
    add x21, x21, x22
    beq x20, x21, test118
    c.addi x16, 0x1
test118:
    li x17, 0xbe78c33e
    li x22, 0x00000369
    sw x23, 0(x20)
    p.sh x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x0000c33e
    beq x18, x19, check118
    c.addi x15, 0x1
check118:
    add x21, x21, x22
    beq x20, x21, test119
    c.addi x16, 0x1
test119:
    li x17, 0x49ffa7b1
    li x22, 0x000072de
    sw x23, 0(x20)
    p.sh x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x0000a7b1
    beq x18, x19, check119
    c.addi x15, 0x1
check119:
    add x21, x21, x22
    beq x20, x21, test120
    c.addi x16, 0x1
test120:
    li x17, 0x98978835
    li x22, 0x00004376
    sw x23, 0(x20)
    p.sh x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x00008835
    beq x18, x19, check120
    c.addi x15, 0x1
check120:
    add x21, x21, x22
    beq x20, x21, test121
    c.addi x16, 0x1
#tests121-126 test the p.sw (register offset). values loaded in and compared to are expected output values
#p.sw instruction is of format "p.sw rs2, rs3(rs1!)". The memory location specified by rs1 is loaded with
#the value of rs2, and then rs1 is post-incremented by the value of rs3
test121:
    li x20, 0x00120000
    li x21, 0x00120000
    li x17, 0x0e38cb05
    li x22, 0x0006616a
    p.sw x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x0e38cb05
    beq x18, x19, check121
    c.addi x15, 0x1
check121:
    add x21, x21, x22
    beq x20, x21, test122
    c.addi x16, 0x1
test122:
    li x17, 0x09e4f2b8
    li x22, 0x00000e6b
    p.sw x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x09e4f2b8
    beq x18, x19, check122
    c.addi x15, 0x1
check122:
    add x21, x21, x22
    beq x20, x21, test123
    c.addi x16, 0x1    
test123:
    li x17, 0x316538b6
    li x22, 0x0000f3d6
    p.sw x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x316538b6
    beq x18, x19, check123
    c.addi x15, 0x1
check123:
    add x21, x21, x22
    beq x20, x21, test124
    c.addi x16, 0x1
test124:
    li x17, 0xd6954e61
    li x22, 0x0000031c
    p.sw x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0xd6954e61
    beq x18, x19, check124
    c.addi x15, 0x1
check124:
    add x21, x21, x22
    beq x20, x21, test125
    c.addi x16, 0x1
test125:
    li x17, 0x3528cd0f
    li x22, 0x0000008f
    p.sw x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x3528cd0f
    beq x18, x19, check125
    c.addi x15, 0x1
check125:
    add x21, x21, x22
    beq x20, x21, test126
    c.addi x16, 0x1
test126:
    li x17, 0x248eb80a
    li x22, 0x00000006
    p.sw x17, x22(x20!)
    lw x18, 0(x21)
    li x19, 0x248eb80a
    beq x18, x19, check126
    c.addi x15, 0x1
check126:
    add x21, x21, x22
    beq x20, x21, test127
    c.addi x16, 0x1
#tests127-132 test the p.sb (register-register). values loaded in and compared to are expected output values
#p.sb instruction is of format "p.sb rs2, rs3(rs1!)". The memory location specified by (rs1+rs3) is loaded with
#the lowest 8 bits of rs2.
test127:
    li x20, 0x00120000
    li x17, 0x6a4acdbc
    li x21, 0x0000fc4a
    add x22, x21, x20
    sw x23, 0(x20)
    p.sb x17, x21(x20)
    lbu x18, 0(x22)
    li x19, 0x000000bc
    beq x18, x19, test128
    c.addi x15, 0x1
test128:
    li x17, 0xdaa2cb67
    li x21, 0x0000032e
    add x22, x21, x20
    sw x23, 0(x20)
    p.sb x17, x21(x20)
    lbu x18, 0(x22)
    li x19, 0x00000067
    beq x18, x19, test129
    c.addi x15, 0x1
test129:
    li x17, 0x04697bc9
    li x21, 0x0000a80c
    add x22, x21, x20
    sw x23, 0(x20)
    p.sb x17, x21(x20)
    lbu x18, 0(x22)
    li x19, 0x000000c9
    beq x18, x19, test130
    c.addi x15, 0x1
test130:
    li x17, 0x5ced4c79
    li x21, 0x0003b7a3
    add x22, x21, x20
    sw x23, 0(x20)
    p.sb x17, x21(x20)
    lbu x18, 0(x22)
    li x19, 0x00000079
    beq x18, x19, test131
    c.addi x15, 0x1
test131:
    li x17, 0x6070b88f
    li x21, 0x00000028
    add x22, x21, x20
    sw x23, 0(x20)
    p.sb x17, x21(x20)
    lbu x18, 0(x22)
    li x19, 0x0000008f
    beq x18, x19, test132
    c.addi x15, 0x1
test132:
    li x17, 0x58df3b46
    li x21, 0x000001f7
    add x22, x21, x20
    sw x23, 0(x20)
    p.sb x17, x21(x20)
    lbu x18, 0(x22)
    li x19, 0x00000046
    beq x18, x19, test133
    c.addi x15, 0x1
#tests133-138 test the p.sh (register-register). values loaded in and compared to are expected output values
#p.sh instruction is of format "p.sh rs2, rs3(rs1)". The memory location specified by (rs1+rs3) is loaded with
#the lower 16 bits of rs2.
test133:
    li x20, 0x00120000
    li x17, 0x00200657
    li x21, 0x0000bc50
    add x22, x21, x20
    sw x23, 0(x20)
    p.sh x17, x21(x20)
    lhu x18, 0(x22)
    li x19, 0x00000657
    beq x18, x19, test134
    c.addi x15, 0x1
test134:
    li x17, 0x7dd36b82
    li x21, 0x00000198
    add x22, x21, x20
    sw x23, 0(x20)
    p.sh x17, x21(x20)
    lhu x18, 0(x22)
    li x19, 0x00006b82
    beq x18, x19, test135
    c.addi x15, 0x1   
test135:
    li x17, 0xf99d2198
    li x21, 0x0000fc55
    add x22, x21, x20
    sw x23, 0(x20)
    p.sh x17, x21(x20)
    lhu x18, 0(x22)
    li x19, 0x00002198
    beq x18, x19, test136
    c.addi x15, 0x1
test136:
    li x17, 0x2ec62ab6
    li x21, 0x00003288
    add x22, x21, x20
    sw x23, 0(x20)
    p.sh x17, x21(x20)
    lhu x18, 0(x22)
    li x19, 0x00002ab6
    beq x18, x19, test137
    c.addi x15, 0x1
test137:
    li x17, 0xc2739a23
    li x21, 0x00000088
    add x22, x21, x20
    sw x23, 0(x20)
    p.sh x17, x21(x20)
    lhu x18, 0(x22)
    li x19, 0x00009a23
    beq x18, x19, test138
    c.addi x15, 0x1
test138:
    li x17, 0x933e16ac
    li x21, 0x00009001
    add x22, x21, x20
    sw x23, 0(x20)
    p.sh x17, x21(x20)
    lhu x18, 0(x22)
    li x19, 0x000016ac
    beq x18, x19, test139
    c.addi x15, 0x1
#tests139-144 test the p.sw (register-register). values loaded in and compared to are expected output values
#p.sw instruction is of format "p.sw rs2, rs3(rs1)". The memory location specified by (rs1+rs3) is loaded with
#the value of rs2.
test139:
    li x20, 0x00120000
    li x17, 0xb30429f5
    li x21, 0x00000d03
    add x22, x21, x20
    p.sw x17, x21(x20)
    lw x18, 0(x22)
    li x19, 0xb30429f5
    beq x18, x19, test140
    c.addi x15, 0x1
test140:
    li x17, 0x6bcc2112
    li x21, 0x00002bf9
    add x22, x21, x20
    p.sw x17, x21(x20)
    lw x18, 0(x22)
    li x19, 0x6bcc2112
    beq x18, x19, test141
    c.addi x15, 0x1   
test141:
    li x17, 0xe9d5ca99
    li x21, 0x0000b608
    add x22, x21, x20
    p.sw x17, x21(x20)
    lw x18, 0(x22)
    li x19, 0xe9d5ca99
    beq x18, x19, test142
    c.addi x15, 0x1
test142:
    li x17, 0x701e48ef
    li x21, 0x00000064
    add x22, x21, x20
    p.sw x17, x21(x20)
    lw x18, 0(x22)
    li x19, 0x701e48ef
    beq x18, x19, test143
    c.addi x15, 0x1
test143:
    li x17, 0x38fd4b41
    li x21, 0x000000c07
    add x22, x21, x20
    p.sw x17, x21(x20)
    lw x18, 0(x22)
    li x19, 0x38fd4b41
    beq x18, x19, test144
    c.addi x15, 0x1
test144:
    li x17, 0x7d43c865
    li x21, 0x0000ec73
    add x22, x21, x20
    p.sw x17, x21(x20)
    lw x18, 0(x22)
    li x19, 0x7d43c865
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

