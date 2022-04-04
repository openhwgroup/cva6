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

#include "corev_uvmt.h"

/* Exception codes */
#define EXCEPTION_ILLEGAL_INSN 2
#define EXCEPTION_BREAKPOINT 3
#define EXCEPTION_ECALL_M 11

.section .text.handlers
.global __no_irq_handler
.global u_sw_irq_handler
.global m_software_irq_handler
.global m_timer_irq_handler
.global m_external_irq_handler
.global m_fast0_irq_handler
.global m_fast1_irq_handler
.global m_fast2_irq_handler
.global m_fast3_irq_handler
.global m_fast4_irq_handler
.global m_fast5_irq_handler
.global m_fast6_irq_handler
.global m_fast7_irq_handler
.global m_fast8_irq_handler
.global m_fast9_irq_handler
.global m_fast10_irq_handler
.global m_fast11_irq_handler
.global m_fast12_irq_handler
.global m_fast13_irq_handler
.global m_fast14_irq_handler
.global m_fast15_irq_handler

.weak m_software_irq_handler
.weak m_timer_irq_handler
.weak m_external_irq_handler
.weak m_fast0_irq_handler
.weak m_fast1_irq_handler
.weak m_fast2_irq_handler
.weak m_fast3_irq_handler
.weak m_fast4_irq_handler
.weak m_fast5_irq_handler
.weak m_fast6_irq_handler
.weak m_fast7_irq_handler
.weak m_fast8_irq_handler
.weak m_fast9_irq_handler
.weak m_fast10_irq_handler
.weak m_fast11_irq_handler
.weak m_fast12_irq_handler
.weak m_fast13_irq_handler
.weak m_fast14_irq_handler
.weak m_fast15_irq_handler

.global glb_illegal_insn_status
.global glb_ebreak_status
.global glb_expect_illegal_insn
.global glb_expect_ebreak_handler
.global glb_exception_ebreak_status
.global glb_expect_irq_entry
.set test_ret_val, CV_VP_STATUS_FLAGS_BASE
.set test_fail, 0x1

/* exception handling */
__no_irq_handler:
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

	la a0, no_exception_handler_msg
	jal ra, puts

    // Check if we expected to enter irq
    la a1, glb_expect_irq_entry
    lw t0, 0(a1)
    beq t0, x0, _irq_fail

    // Clear entry flag
    li t0, 0
    sw t0, 0(a1)
	//j __no_irq_handler

    // Return
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

_irq_fail:
    li a0, CV_VP_STATUS_FLAGS_BASE
    li t0, test_fail
    sw t0, 0(a0)
    ret

u_sw_irq_handler:
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
	la a0, ecall_msg
	jal ra, handle_syscall
	j end_handler_incr_mepc

m_software_irq_handler:
    j __no_irq_handler

m_timer_irq_handler:
	j __no_irq_handler

m_external_irq_handler:
	j __no_irq_handler

m_fast0_irq_handler:
	j __no_irq_handler

m_fast1_irq_handler:
	j __no_irq_handler

m_fast2_irq_handler:
	j __no_irq_handler

m_fast3_irq_handler:
	j __no_irq_handler

m_fast4_irq_handler:
	j __no_irq_handler

m_fast5_irq_handler:
	j __no_irq_handler

m_fast6_irq_handler:
	j __no_irq_handler

m_fast7_irq_handler:
	j __no_irq_handler

m_fast8_irq_handler:
	j __no_irq_handler

m_fast9_irq_handler:
	j __no_irq_handler

m_fast10_irq_handler:
	j __no_irq_handler

m_fast11_irq_handler:
	j __no_irq_handler

m_fast12_irq_handler:
	j __no_irq_handler

m_fast13_irq_handler:
	j __no_irq_handler

m_fast14_irq_handler:
	j __no_irq_handler

m_fast15_irq_handler:
	j __no_irq_handler


handle_ebreak:
	/* TODO support debug handling requirements.  */
	la a0, ebreak_msg
	jal ra, puts
        // Check if expecting ebreak handler
        la a0, glb_expect_ebreak_handler
        lw t0, 0(a0)
        bne t0, x0, cont_handle_ebreak
        // Not expecting ebreak, assert test failed
        li a0, CV_VP_STATUS_FLAGS_BASE
        li t0, 1
        sw t0, 0(a0)
	j end_handler_incr_mepc
cont_handle_ebreak:
        //increment hart status
        sw x0, 0(a0)
        la a0, glb_ebreak_status
        lw t0, 0(a0)
        addi t0,t0,1
        sw t0, 0(a0)
	j end_handler_incr_mepc



handle_illegal_insn:
	la a0, illegal_insn_msg
	jal ra, puts
        // Check if expecting illegal instruction
        la a0, glb_expect_illegal_insn
        lw t0, 0(a0)
        bne t0, x0, cont_illegal_insn
        li a0, CV_VP_STATUS_FLAGS_BASE
        li t0, 1
        sw t0, 0(a0)            //Test Failed
	j end_handler_incr_mepc
cont_illegal_insn:
        //increment hart status
        sw x0, 0(a0)
        la a0, glb_illegal_insn_status
        lw t0, 0(a0)
        addi t0,t0,1
        sw t0, 0(a0)

        // Check if we are expected to execute ebreak
        la a0, glb_exception_ebreak_status
        lw t0, 0(a0)
        //  End handler if no ebreak is to be executed
        beq t0, x0, end_handler_incr_mepc

        // Clear ebreak flag
        sw x0, 0(a0)
        // Execute ebreak
        .4byte 0x00100073
        // Exit handler
    	j end_handler_incr_mepc

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
	.string "illegal instruction exception handler entered\n"
ecall_msg:
	.string "ecall exception handler entered\n"
ebreak_msg:
	.string "ebreak exception handler entered\n"
unknown_msg:
	.string "unknown exception handler entered\n"
no_exception_handler_msg:
	.string "no exception handler installed\n"
