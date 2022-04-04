#Copyright 202[x] Silicon Labs, Inc.

#This file, and derivatives thereof are licensed under the
#Solderpad License, Version 2.0 (the "License");
#Use of this file means you agree to the terms and conditions
#of the license and are in full compliance with the License.
#You may obtain a copy of the License at
#
#    https://solderpad.org/licenses/SHL-2.0/
#
#Unless required by applicable law or agreed to in writing, software
#and hardware implementations thereof
#distributed under the License is distributed on an "AS IS" BASIS,
#WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
#See the License for the specific language governing permissions and
#limitations under the License.

#include "corev_uvmt.h"

.section .single_step_code_sect, "ax"
.set timer_reg_addr, CV_VP_INTR_TIMER_BASE+0
.set timer_val_addr, CV_VP_INTR_TIMER_BASE+4
.set test_ret_val,   CV_VP_STATUS_FLAGS_BASE
.set test_fail, 0x1

.global glb_step_info
.global glb_expect_debug_entry
.global glb_expect_illegal_insn
.global glb_expect_irq_entry
.global _step_trig_point
.global _step_trig_exit
.global _single_step


_single_step:
        addi sp,sp,-30
        sw t0, 0(sp)
        sw t1, 4(sp)
        sw a0, 8(sp)
        sw a1, 12(sp)
        sw a2, 16(sp)
        sw ra, 20(sp)

    // Expect debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    // Set step cause to 1 - enable single stepping
    la a1, glb_step_info
    li t0, 1
    sw t0, 0(a1)

    // Set t0 to 0
    li t0, 0

    // Enter debug mode to execute cause=1
    c.ebreak

    // To check if debug code increments DPC correctly,
    // Load up t0 in first instruction after ebreak
    li t0, 1
    beq t0, x0, _single_step_fail

    // We are single stepping, WFI should complete as NOP
    // Test will hang here if WFI is not converted properly
    wfi

    // illegal instruction
    la a1, glb_expect_illegal_insn
    li t0, 1
    sw t0, 0(a1)

    la a1, glb_step_info
    li t0, 3
    sw t0, 0(a1)

    csrr t0, dcsr // illegal

    la a1, glb_expect_illegal_insn
    li t0, 1
    sw t0, 0(a1)
    dret // illegal

    // Trigger match setup
    la a1, glb_step_info
    li t0, 4
    sw t0, 0(a1)
    nop
    nop
    li t0, 0

_step_trig_point:
    li t0, 1 // trig here

_step_trig_exit:
    addi t0, t0,2 // debug code moves dpc to here
    li t1, 2
    // If trigger was correct, debug code skips
    // loading of t0 to 1, and t0 should be of value 2
    bne t0, t1, _single_step_fail


    //-----------------
    // Stepping with interrupt, stepie=1
    la a1, glb_step_info
    li t0, 5
    sw t0, 0(a1)

    // Expect irq flag
    la a1, glb_expect_irq_entry
    li t0, 1
    sw t0, 0(a1)

    // Assert irq
    li a1, timer_reg_addr
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 2
    sw t0, 0(a1)

_irq_wait_loop:
    la a1, glb_expect_irq_entry
    lw t0, 0(a1);
    bne t0, x0, _irq_wait_loop


    //-----------------
    // Stepping with interrupt, stepie=0
    la a1, glb_step_info
    li t0, 6
    sw t0, 0(a1)

    // Assert irq
    li a1, timer_reg_addr
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 2
    sw t0, 0(a1)

    // Wait out some instructions to give IRQ a chance
    // Report an ERROR if IRQ taken as we did not set glb_expect_irq_entry flag
    nop
    nop
    nop
    nop

    // De-Assert irq
    li a1, timer_reg_addr
    li t0, 0x00000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 1
    sw t0, 0(a1)

    nop
    nop

    # set step reason to 7 (step with c.ebreak)
    la a1, glb_step_info
    li t0, 7
    sw t0, 0(a1)

    # Ebreak to cover ebreak vs step cause priority
    c.ebreak

    # set step reason to 8 (step with ebreak)
    la a1, glb_step_info
    li t0, 8
    sw t0, 0(a1)

    # Ebreak to cover ebreak vs step cause priority
    .4byte 0x00100073

    # Set step reason to 9, ebreak without dcsr.ebreakm
    la a1, glb_step_info
    li t0, 9
    sw t0, 0(a1)

    # Expect to enter ebreak handler
    la a0, glb_expect_ebreak_handler
    li t0, 1
    sw t0, 0(a0)

    .4byte 0x00100073

     # Expect to enter ebreak handler
    la a0, glb_expect_ebreak_handler
    li t0, 1
    sw t0, 0(a0)
    # Set step reason to 10, cebreak without dcsr.ebreakm
    la a1, glb_step_info
    li t0, 10
    sw t0, 0(a1)

    c.ebreak

    # set step reason to 0, normal step
    la a1, glb_step_info
    li t0, 0
    sw t0, 0(a1)

    ecall
    // Cause 2, disable single stepping
    la a1, glb_step_info
    li t0, 2
    sw t0, 0(a1)
    nop
    nop
    j _single_step_done

_single_step_fail:
    li a0, CV_VP_STATUS_FLAGS_BASE
    li t0, test_fail
    sw t0, 0(a0)
    // Turn off single step
    la a1, glb_step_info
    li t0, 2
    sw t0, 0(a1)

    j _single_step_done

_single_step_done:
        lw t0, 0(sp)
        lw t1, 4(sp)
        lw a0, 8(sp)
        lw a1, 12(sp)
        lw a2, 16(sp)
        lw ra, 20(sp)
        addi sp,sp,30
	ret
