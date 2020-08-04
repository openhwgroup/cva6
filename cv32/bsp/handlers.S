/*
* Copyright 2019 ETH Zürich and University of Bologna
*
* Licensed under the Apache License, Version 2.0 (the "License");
* you may not use this file except in compliance with the License.
* You may obtain a copy of the License at
*
*     http://www.apache.org/licenses/LICENSE-2.0
*
* Unless required by applicable law or agreed to in writing, software
* distributed under the License is distributed on an "AS IS" BASIS,
* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
* See the License for the specific language governing permissions and
* limitations under the License.
*/

/* Exception codes */
#define EXCEPTION_ILLEGAL_INSN 2
#define EXCEPTION_BREAKPOINT 3
#define EXCEPTION_ECALL_M 11

.section .text.handlers
.global __no_irq_handler
.global sw_irq_handler
.global verification_irq_handler
.global software_irq_handler
.global timer_irq_handler
.global external_irq_handler
.global fast0_irq_handler
.global fast1_irq_handler
.global fast2_irq_handler
.global fast3_irq_handler
.global fast4_irq_handler
.global fast5_irq_handler
.global fast6_irq_handler
.global fast7_irq_handler
.global fast8_irq_handler
.global fast9_irq_handler
.global fast10_irq_handler
.global fast11_irq_handler
.global fast12_irq_handler
.global fast13_irq_handler
.global fast14_irq_handler
.global fast15_irq_handler

.weak software_irq_handler
.weak timer_irq_handler
.weak external_irq_handler
.weak fast0_irq_handler
.weak fast1_irq_handler
.weak fast2_irq_handler
.weak fast3_irq_handler
.weak fast4_irq_handler
.weak fast5_irq_handler
.weak fast6_irq_handler
.weak fast7_irq_handler
.weak fast8_irq_handler
.weak fast9_irq_handler
.weak fast10_irq_handler
.weak fast11_irq_handler
.weak fast12_irq_handler
.weak fast13_irq_handler
.weak fast14_irq_handler
.weak fast15_irq_handler


/* exception handling */
__no_irq_handler:
	la a0, no_exception_handler_msg
	jal ra, puts
	j __no_irq_handler

software_irq_handler:
	j __no_irq_handler

timer_irq_handler:
	j __no_irq_handler

external_irq_handler:
	j __no_irq_handler

fast0_irq_handler:
	j __no_irq_handler

fast1_irq_handler:
	j __no_irq_handler

fast2_irq_handler:
	j __no_irq_handler

fast3_irq_handler:
	j __no_irq_handler

fast4_irq_handler:
	j __no_irq_handler

fast5_irq_handler:
	j __no_irq_handler

fast6_irq_handler:
	j __no_irq_handler

fast7_irq_handler:
	j __no_irq_handler

fast8_irq_handler:
	j __no_irq_handler

fast9_irq_handler:
	j __no_irq_handler

fast10_irq_handler:
	j __no_irq_handler

fast11_irq_handler:
	j __no_irq_handler

fast12_irq_handler:
	j __no_irq_handler

fast13_irq_handler:
	j __no_irq_handler

fast14_irq_handler:
	j __no_irq_handler

fast15_irq_handler:
	j __no_irq_handler

sw_irq_handler:
	/* While we are still using puts in handlers, save all caller saved
	   regs.  Eventually, some of these saves could be deferred.  */
	addi sp,sp,-64
	sw ra, 0(sp)
	sw a0, 4(sp)
	sw a1, 8(sp)
	sw a2, 12(sp)
	sw a3, 16(sp)
	sw a4, 20(sp)
	sw a5, 24(sp)
	sw a6, 28(sp)
	sw a7, 32(sp)
	sw t0, 36(sp)
	sw t1, 40(sp)
	sw t2, 44(sp)
	sw t3, 48(sp)
	sw t4, 52(sp)
	sw t5, 56(sp)
	sw t6, 60(sp)
	csrr t0, mcause
	li t1, EXCEPTION_ILLEGAL_INSN
	beq t0, t1, handle_illegal_insn
	li t1, EXCEPTION_ECALL_M
	beq t0, t1, handle_ecall
	li t1, EXCEPTION_BREAKPOINT
	beq t0, t1, handle_ebreak
	j handle_unknown

handle_ecall:
	jal ra, handle_syscall
	j end_handler_incr_mepc

handle_ebreak:
	/* TODO support debug handling requirements.  */
	la a0, ebreak_msg
	jal ra, puts
	j end_handler_incr_mepc

handle_illegal_insn:
	la a0, illegal_insn_msg
	jal ra, puts
	j end_handler_incr_mepc

handle_unknown:
	la a0, unknown_msg
	jal ra, puts
	/* We don't know what interrupt/exception is being handled, so don't
	   increment mepc.  */
	j end_handler_ret

end_handler_incr_mepc:
	csrr t0, mepc
	lb t1, 0(t0)
	li a0, 0x3
	and t1, t1, a0
	/* Increment mepc by 2 or 4 depending on whether the instruction at mepc
	   is compressed or not.  */
	bne t1, a0, end_handler_incr_mepc2
	addi t0, t0, 2
end_handler_incr_mepc2:
	addi t0, t0, 2
	csrw mepc, t0
end_handler_ret:
	lw ra, 0(sp)
	lw a0, 4(sp)
	lw a1, 8(sp)
	lw a2, 12(sp)
	lw a3, 16(sp)
	lw a4, 20(sp)
	lw a5, 24(sp)
	lw a6, 28(sp)
	lw a7, 32(sp)
	lw t0, 36(sp)
	lw t1, 40(sp)
	lw t2, 44(sp)
	lw t3, 48(sp)
	lw t4, 52(sp)
	lw t5, 56(sp)
	lw t6, 60(sp)
	addi sp,sp,64
	mret
/* this interrupt can be generated for verification purposes, random or when the
   PC is equal to a given value*/
verification_irq_handler:
	mret

.section .rodata
illegal_insn_msg:
	.string "CV32E40P BSP: illegal instruction exception handler entered\n"
ecall_msg:
	.string "CV32E40P BSP: ecall exception handler entered\n"
ebreak_msg:
	.string "CV32E40P BSP: ebreak exception handler entered\n"
unknown_msg:
	.string "CV32E40P BSP: unknown exception handler entered\n"
no_exception_handler_msg:
	.string "CV32E40P BSP: no exception handler installed\n"
