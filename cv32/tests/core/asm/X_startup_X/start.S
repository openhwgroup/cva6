#ifndef TOP_OF_STACK
#   define TOP_OF_STACK 0x13000
#endif

.global _setup_stack
.global _trap_vector
.global _exit

.global _trap_Generic_Handler
.global _trap_Machine_Software_Interrupt
.global _trap_Machine_External_Interrupt
.global _trap_Machine_Timer_Interrupt

.global _clrINTC

.global _intack
.global _boot_value
.global _test_stdout
.global _test_intc_machine_external
.global _test_intc_machine_software
.global _test_intc_machine_timer    

#undef SX
#undef LX
#ifdef RISCV32
    #define SX sw
    #define LX lw
#else
    #define SX sd
    #define LX ld
#endif

.macro PUSH_REGS
    addi    sp,sp,-140
    SX      ra,136(sp)
    SX      t0,128(sp)
    SX      t1,120(sp)
    SX      t2,112(sp)
    SX      t3,104(sp)
    SX      t4,96(sp)
    SX      t5,88(sp)
    SX      t6,80(sp)
    SX      a0,72(sp)
    SX      a1,64(sp)
    SX      a2,56(sp)
    SX      a3,48(sp)
    SX      a4,40(sp)
    SX      a5,32(sp)
    SX      a6,24(sp)
    SX      a7,16(sp)
    SX      s0,8(sp)
    addi    s0,sp,144
.endm

.macro POP_REGS
    LX      ra,136(sp)
    LX      t0,128(sp)
    LX      t1,120(sp)
    LX      t2,112(sp)
    LX      t3,104(sp)
    LX      t4,96(sp)
    LX      t5,88(sp)
    LX      t6,80(sp)
    LX      a0,72(sp)
    LX      a1,64(sp)
    LX      a2,56(sp)
    LX      a3,48(sp)
    LX      a4,40(sp)
    LX      a5,32(sp)
    LX      a6,24(sp)
    LX      a7,16(sp)
    LX      s0,8(sp)
    addi    sp,sp,140
.endm
	
# boot code
.section .reset_vector,"ax"
 _reset_vector:
    # Point to trap handler code
    la a0, _trap_vector
    csrw mtvec, a0
    # Setup stack pointer
    li sp, TOP_OF_STACK
    # jump to staert
    j _start
    #j _setup_stack

.section .trap_vector,"ax"
_trap_vector:
/* code        routine */
/* 00 */  j _trap_Generic_Handler_ASM
/* 01 */  j _trap_Generic_Handler_ASM
/* 02 */  j _trap_Generic_Handler_ASM
/* 03 */  j _trap_Machine_Software_Interrupt_ASM
/* 04 */  j _trap_Generic_Handler_ASM
/* 05 */  j _trap_Generic_Handler_ASM
/* 06 */  j _trap_Generic_Handler_ASM
/* 07 */  j _trap_Machine_Timer_Interrupt_ASM
/* 08 */  j _trap_Generic_Handler_ASM
/* 09 */  j _trap_Generic_Handler_ASM
/* 10 */  j _trap_Generic_Handler_ASM
/* 11 */  j _trap_Machine_External_Interrupt_ASM
/* RSVD */

.text

_trap_Machine_Software_Interrupt_ASM:
    PUSH_REGS
    jal ra, _trap_Machine_Software_Interrupt
    jal ra, _clrINTC_machine_software
    POP_REGS
    mret

_trap_Machine_Timer_Interrupt_ASM:
    PUSH_REGS
    jal ra, _trap_Machine_Timer_Interrupt
    jal ra, _clrINTC_machine_timer
    POP_REGS
    mret

_trap_Generic_Handler_ASM:
    PUSH_REGS
    jal ra, _trap_Generic_Handler
/*    jal ra, _clrINTC */
    POP_REGS
    mret

_trap_Machine_External_Interrupt_ASM:
    PUSH_REGS
    jal ra, _trap_Machine_External_Interrupt
    jal ra, _clrINTC_machine_external
    POP_REGS
    mret

_test_exit:
    j _test_exit

# Redefine _exit
_exit:
    j _test_exit

.align 4
.data

_boot_value:
.word 0x0

_intack:
.word 0x0

.section .tty,"aw"
_test_stdout:
.word 0x0

_test_intc_machine_external:
.word 0x0
        
_test_intc_machine_software:
.word 0x0

_test_intc_machine_timer:
.word 0x0
        
        

	
