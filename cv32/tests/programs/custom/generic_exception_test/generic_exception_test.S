.globl _start
.globl main
.globl exit
.global debug
.section .text
.global test_results
.global u_sw_irq_handler
test_results:
	.word 123456789
# main test
main:
    li x15, 0x00001800
    csrrw x0, mstatus, x15  # redundant in cv32e40p: hardwired PoR value
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
    li x16, 0x0
    li x17, 0xf61163af
    li x18, 0x0
    li x19, 0x0
    li x20, 0xc552e854
    li x21, 0xc553e854
    li x22, 0xf3ae47cd
    li x23, 0x0
    li x24, 0x00012000
    li x25, 0x80000000
    li x26, 0x0
    li x27, 0xffa38c28
    li x28, 0xf915a8c7
    li x29, 0x9
    li x30, 0x0
    li x31, 0x5912efde
    li x4, 0x40001104
    csrrc x30, mtvec, x0
#    csrrc x30, mtvec, 0x0
#2220.000 ns: Illegal instruction (core 0) at PC 0x0000017c:
    .word(0x00000000)	#Exception Code: 2 (illegal instruction)
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    c.ebreak	#Exception Code: 3 (breakpoint)
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    ebreak		#Exception Code: 3 (breakpoint)
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    ecall		#Exception Code: 11 (env call from M-mode)
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    c.addi sp, -8
    sw t0, 4(sp)
    li x15, 0x00001808
    csrs mstatus, x15
    lw t0, 4(sp)
    c.addi sp, 8
#6645.000 ns: Illegal instruction (core 0) at PC 0x000001ec:
    .word(0x00000000)	#Exception Code: 2
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    c.ebreak	#Exception Code: 3
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    ebreak		#Exception Code: 3
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    ecall		#Exception Code: 11
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
    lw x0, 0(x24)	#No Exception
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
#11118.000 ns: Illegal instruction (core 0) at PC 0x00000260:
    .word(0x0057179B)   #Exception Code: 2 #SLLIW
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
#12186.000 ns: Illegal instruction (core 0) at PC 0x00000278:
    .word(0x0057579B)   #Exception Code: 2 #SRLIW
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
#13254.000 ns: Illegal instruction (core 0) at PC 0x00000290:
    .word(0x4057579B)   #Exception Code: 2 #SRAIW
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
#14322.000 ns: Illegal instruction (core 0) at PC 0x000002a8:
    csrrc x17, 0x7B0, x0 #Exception Code: 2 #Cannot access DCSR in M mode
    li x18, 0x00008000
    or x17, x17, x18
#15306.000 ns: Illegal instruction (core 0) at PC 0x000002b2:
    csrrw x0, 0x7B0, x17 #Exception Code: 2 #Cannot access DCSR in M mode
#16290.000 ns: Illegal instruction (core 0) at PC 0x000002b6:
    csrrc x17, 0x7B0, x0 #Exception Code: 2 #Cannot access DCSR in M mode
    add x17, x1, x0
    c.addi x17, 12
#17265.000 ns: Illegal instruction (core 0) at PC 0x000002c0:
    csrrw x0, 0x7B1, x17 #Exception Code: 2 #Cannot access DPC in M mode
#18246.000 ns: Illegal instruction (core 0) at PC 0x000002c4:
    csrrc x17, 0x7B1, x0 #Exception Code: 2 #Cannot access DPC in M mode
    ebreak
    nop
    nop
    csrrc x14, mstatus, x0
    csrrw x0, mstatus, x15
    csrrc x14, mstatus, x0
    nop
    nop
added_by_mike:
    .word(0x3bc6f92f)
    .word(0x5dd26da7)
    .word(0xe5607a57)
    .word(0x958e4a67)
    .word(0x6159607b)
    .word(0x6c6b7433)
    .word(0x1a6a2b33)
    .word(0xd9067c3b)
    .word(0xfa133223)
#    .word(0x4b724b57)
    .word(0x6fcbc273)
    .word(0x395dd7e7)
exit:
    lw x18, test_results /* report passed result */
#    li x16, 0x25a
#    beq x26, x16, test_end
#    li x18, 1
test_end:
    li x17, 0x20000000
    sw x18,0(x17)
    j _exit

u_sw_irq_handler:
    addi    sp,sp,-120
    sw      x1,116(sp)
    sw      x2,112(sp)
    sw      x3,108(sp)
    sw      x4,104(sp)
    sw      x5,100(sp)
    sw      x6,96(sp)
    sw      x7,92(sp)
    sw      x8,88(sp)
    sw      x9,84(sp)
    sw      x10,80(sp)
    sw      x11,76(sp)
    sw      x12,72(sp)
    sw      x13,68(sp)
    sw      x14,64(sp)
    sw      x15,60(sp)
    sw      x16,56(sp)
    sw      x17,52(sp)
    sw      x18,48(sp)
    sw      x19,44(sp)
    sw      x20,40(sp)
    sw      x21,36(sp)
    sw      x22,32(sp)
    sw      x23,28(sp)
    sw      x24,24(sp)
    sw      x25,20(sp)
    sw      x28,16(sp)
    sw      x29,12(sp)
    sw      x30,8(sp)
    sw      x31,4(sp)
    c.addi x27, 1
    csrrc x31, mtvec, x0
    beq x31, x30, continue_check
    lui a3, 0x1
    add x26, x26, a3
continue_check:
    li t6, 0xf
    csrrc t5, mcause, x0
    and t6, t6, t5
    li t4, 2
    bne t6, t4, _check_3
    addi x26, x26, 0x1
    csrrc s0, mepc, x0
    c.addi s0, 4
    csrrw x0, mepc, s0
    j _end_trap_Generic_Handler_ASM
_check_3:
    li t4, 3
    bne t6, t4, _check_11
    addi x26, x26, 0x10
    csrrc s0, mepc, x0
    c.addi s0, 2
    csrrw x0, mepc, s0
    j _end_trap_Generic_Handler_ASM
_check_11:
    li t4, 11
    bne t6, t4, _end_trap_Generic_Handler_ASM
    addi x26, x26, 0x100
    csrrc s0, mepc, x0
    c.addi s0, 4
    csrrw x0, mepc, s0
_end_trap_Generic_Handler_ASM:
    lw      x1,116(sp)
    lw      x2,112(sp)
    lw      x3,108(sp)
    lw      x4,104(sp)
    lw      x5,100(sp)
    lw      x6,96(sp)
    lw      x7,92(sp)
    lw      x8,88(sp)
    lw      x9,84(sp)
    lw      x10,80(sp)
    lw      x11,76(sp)
    lw      x12,72(sp)
    lw      x13,68(sp)
    lw      x14,64(sp)
    lw      x15,60(sp)
    lw      x16,56(sp)
    lw      x17,52(sp)
    lw      x18,48(sp)
    lw      x19,44(sp)
    lw      x20,40(sp)
    lw      x21,36(sp)
    lw      x22,32(sp)
    lw      x23,28(sp)
    lw      x24,24(sp)
    lw      x25,20(sp)
    lw      x28,16(sp)
    lw      x29,12(sp)
    lw      x30,8(sp)
    lw      x31,4(sp)
    addi    sp,sp,120
    mret
    
_exit:
    j _exit

debug:
    j _exit
