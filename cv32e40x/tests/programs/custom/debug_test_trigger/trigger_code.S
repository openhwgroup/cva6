#Copyright 202[x] Silicon Labs, Inc.
#
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

.section .trigger_code_sect, "ax"
.set test_ret_val, CV_VP_STATUS_FLAGS_BASE
.set test_fail, 0x1
.set timer_reg_addr, CV_VP_INTR_TIMER_BASE
.set timer_val_addr, CV_VP_INTR_TIMER_BASE+4
.set debug_req_reg,  CV_VP_DEBUG_CONTROL_BASE
.global _trigger_exit
.global _trigger_test
.global _trigger_code
.global _trigger_test_ebreak
.global _trigger_code_ebreak
.global _trigger_code_illegal_insn
.global _trigger_code_branch_insn
.global _trigger_code_multicycle_insn
.global _trigger_code_cebreak
.global _trigger_test_combo
.global glb_hart_status
.global glb_expect_debug_entry
.global glb_expect_irq_entry
.global glb_expect_illegal_insn
.global glb_debug_status
.type _trigger_code, @function
.type _trigger_code_ebreak, @function
.type _trigger_code_cebreak, @function
.type _trigger_code_illegal_insn, @function
.type _trigger_code_branch_insn, @function
.type _trigger_code_multicycle_insn, @function
#.type _trigger_test_combo, @function

_trigger_code_ebreak:
    .4byte 0x00100073
    ret

_trigger_code_cebreak:
    c.ebreak
    ret

_trigger_code_illegal_insn:
    dret
    ret

_trigger_code_branch_insn:
    beq t0, t1, __trigger_fail
    ret

_trigger_code_multicycle_insn:
    mulhsu t0, t0, t1
    ret

_trigger_test_ebreak:
    addi sp,sp,-30
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw a0, 8(sp)
    sw a1, 12(sp)
    sw a2, 16(sp)
    sw ra, 20(sp)

    # a0 holds argument
    # 0 - ebreak
    # 1 - c.c.ebreak
    # 2 - illegal instruction
    # 3 - branch instruction
    # 4 - multicycle instruction (mulhsu)

    mv t1, a0
    li t0, 0
    beq t0, t1, _jmp_ebreak

    li t0, 1
    beq t0, t1, _jmp_cebreak

    li t0, 2
    beq t0, t1, _jmp_illegal_insn

    li t0, 3
    beq t0, t1, _jmp_branch_insn

    li t0, 4
    beq t0, t1, _jmp_multicycle_insn

_jmp_ebreak:
    jal ra, _trigger_code_ebreak
    j __trigger_done
_jmp_cebreak:
    jal ra, _trigger_code_cebreak
    j __trigger_done
_jmp_illegal_insn:
    jal ra, _trigger_code_illegal_insn
    j __trigger_done
_jmp_branch_insn:
    jal ra, _trigger_code_branch_insn
    j __trigger_done
_jmp_multicycle_insn:
    jal ra, _trigger_code_multicycle_insn
    j __trigger_done

# Enter debug mode to set tdata1 and tdata2 for triggering on execution of instruction at _trigger_code
_trigger_setup:
    addi sp,sp,-8
    sw ra, 4(sp)

    # Don't expect trigger match
    li a0, 0
    jal ra, _trigger_test

    # Setup trigger
    la a1, glb_hart_status
    li t0, 7
    sw t0, 0(a1)

    # expect debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # Assert debug_req
    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x8) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0xc8)
    sw t0, 0(a1)
_wait1:
    la a1, glb_hart_status
    lw t0, 0(a1)
    la a1, glb_debug_status
    lw t1, 0(a1)
    bne t0, t1, _wait1

    // Check csrs
    csrr t0, 0x7A1
    li t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1<<2
    bne t0, t1, __trigger_fail

    csrr t0, 0x7A2
    la t1, _trigger_code
    bne t0, t1, __trigger_fail

    lw ra, 4(sp)
    addi sp,sp,8

    ret

# Assembly code for generating
# cycle accurate debug_req
# and irq
_trigger_test_combo:
    addi sp,sp,-30
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw a0, 8(sp)
    sw a1, 12(sp)
    sw a2, 16(sp)
    sw ra, 20(sp)

    jal ra, _trigger_setup

    # ----------------------------------------------------
    # Test 10: Expect trigger and return to the same instruction
    # Debugger will clear tdata[2] to avoid re-triggering upon return
    # ----------------------------------------------------
    la a1, glb_hart_status
    li t0, 10
    sw t0, 0(a1)

    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # execute trigger code
    li a0, 0
    jal ra, _trigger_test

    # Re-set the triger to re-enable
    jal ra, _trigger_setup

    # ----------------------------------------------------
    # Test 8: Expect trigger with dpc changed in debugger handler to avoid
    # ----------------------------------------------------
    la a1, glb_hart_status
    li t0, 8
    sw t0, 0(a1)

    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # execute trigger code
    li a0, 1
    jal ra, _trigger_test

_wait2:
    la a1, glb_hart_status
    lw t0, 0(a1)
    la a1, glb_debug_status
    lw t1, 0(a1)
    bne t0, t1, _wait2

    # Setup trigger again
    la a1, glb_hart_status
    li t0, 7
    sw t0, 0(a1)

    # expect debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # Assert debug_req
    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x8) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0xc8)
    sw t0, 0(a1)
_wait3:
    la a1, glb_hart_status
    lw t0, 0(a1)
    la a1, glb_debug_status
    lw t1, 0(a1)
    bne t0, t1, _wait3

    # ----------------------------------------------------
    # debug_req and trigger on same cycle
    # ----------------------------------------------------
    # Set hart status
    la a1, glb_hart_status
    li t0, 8
    sw t0, 0(a1)

    # set expected debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # Enable debug_req in VP
    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x5) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0x5)
    sw t0, 0(a1)

    # Call trigger function
    li a0, 1
    jal ra, _trigger_code

    # ----------------------------------------------------
    # debug_req and irq when trigger on ebreak
    # ----------------------------------------------------
    # Set hart status
    la a1, glb_hart_status
    li t0, 81
    sw t0, 0(a1)

    # set expected debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # set expected irq
    la a1, glb_expect_irq_entry
    li t0, 1
    sw t0, 0(a1)

    # ----------------------------------------------------
    # Enable debug_req in VP
    # ----------------------------------------------------
    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x5) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0x1c)
    sw t0, 0(a1)

    # Enable interrupt
    li a1, timer_reg_addr
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 18
    sw t0, 0(a1)

    # Call trigger function
    li a0, 0
    jal ra, _trigger_test_ebreak

    # ----------------------------------------------------
    # debug_req and irq when trigger on c.ebreak
    # ----------------------------------------------------
    # Set hart status
    la a1, glb_hart_status
    li t0, 82
    sw t0, 0(a1)

    # set expected debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # set expected irq
    la a1, glb_expect_irq_entry
    li t0, 1
    sw t0, 0(a1)

    # Enable debug_req in VP
    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x5) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0x1c)
    sw t0, 0(a1)

    # Enable interrupt
    li a1, timer_reg_addr
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 19
    sw t0, 0(a1)

    # Call trigger function
    li a0, 1
    jal ra, _trigger_test_ebreak

    # ----------------------------------------------------
    # debug_req and irq when trigger on illegal insn
    # ----------------------------------------------------
    # Set hart status
    la a1, glb_hart_status
    li t0, 83
    sw t0, 0(a1)

    # set expected debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # set expected irq
    la a1, glb_expect_irq_entry
    li t0, 1
    sw t0, 0(a1)

    # Enable debug_req in VP
    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x5) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0x20)
    sw t0, 0(a1)

    # Enable interrupt
    li a1, timer_reg_addr
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 23
    sw t0, 0(a1)

    # Call trigger function
    li a0, 2
    jal ra, _trigger_test_ebreak

    # ----------------------------------------------------
    # debug_req and irq when trigger on branch insn
    # ----------------------------------------------------
    # Set hart status
    la a1, glb_hart_status
    li t0, 84
    sw t0, 0(a1)

    # set expected debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # set expected irq
    la a1, glb_expect_irq_entry
    li t0, 1
    sw t0, 0(a1)

    # Enable debug_req in VP
    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x5) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0x20)
    sw t0, 0(a1)

    # Enable interrupt
    li a1, timer_reg_addr
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 23
    sw t0, 0(a1)

    # Call trigger function
    li a0, 3
    jal ra, _trigger_test_ebreak

    # ----------------------------------------------------
    # debug_req and irq when trigger on multicycle insn
    # ----------------------------------------------------
    # Set hart status
    la a1, glb_hart_status
    li t0, 85
    sw t0, 0(a1)

    # set expected debug
    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    # set expected irq
    la a1, glb_expect_irq_entry
    li t0, 1
    sw t0, 0(a1)

    # Enable debug_req in VP
    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x5) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0x24)
    sw t0, 0(a1)

    # Enable interrupt
    li a1, timer_reg_addr
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 27
    sw t0, 0(a1)

    # Call trigger function
    li a0, 4
    jal ra, _trigger_test_ebreak

    # Trigger disabled
    la a1, glb_hart_status
    li t0, 9
    sw t0, 0(a1)

    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x5) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0x1)
    sw t0, 0(a1)
    nop
    nop
    nop

    li a0, 0
    jal ra, _trigger_test

    la a1, glb_debug_status
    lw t0, 0(a1)
    li t1, 9
    bne t0, t1, __trigger_fail

    # ----------------------------------------------------
    # trigger match in debug mode
    # ----------------------------------------------------
    la a1, glb_hart_status
    li t0, 15
    sw t0, 0(a1)

    la a1, glb_expect_debug_entry
    li t0, 1
    sw t0, 0(a1)

    li a1, debug_req_reg
    li t0, CV_VP_DEBUG_CONTROL_DBG_REQ(0x1) | \
           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1) | \
           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x5) | \
           CV_VP_DEBUG_CONTROL_START_DELAY(0x1)
    sw t0, 0(a1)
    nop
    nop

    la a1, glb_debug_status
    lw t0, 0(a1)
    li t1, 15
    bne t0, t1, __trigger_fail

    j __trigger_done


     // We will trigger on the _trigger_code addess
	// We should not expect the first instruction to execute
	// The debugger code will move the PC to the trigger_exit_code
     // We will trigger on the _trigger_code addess
_trigger_code:
        add a2,a0,a1
        ret
_trigger_exit:
        ret
_trigger_test:
        addi sp,sp,-30
        sw t0, 0(sp)
        sw t1, 4(sp)
        sw a0, 8(sp)
        sw a1, 12(sp)
        sw a2, 16(sp)
        sw ra, 20(sp)

	// a0 holds input to function (expect trigger)
	mv t1, a0

	// Load up some random data to add
	li a0, 7893
	li a1, 1452
	li a2,  191 // a2 value will be overwrriten by _trigger_code
	mv t2,  a2  // keep a copy of the value to compare against

	// Call function that will have a trigger match
	//   If no trigger match, then a2=a0+a1
	//   Else if trigger matched, then a2 is not modified
	jal ra, _trigger_code

	// if (expect trigger) check against original value (in t2)
	bne t1 ,x0, __trigger_check
	// else
	// trigger match not expected, function executes as normal
	// set execpted value to t2 = a0 + a1
	add t2, a0, a1
__trigger_check:
	beq t2,a2,__trigger_done
__trigger_fail:
        li a0, CV_VP_STATUS_FLAGS_BASE
        li t0, 1
        sw t0, 0(a0)
__trigger_done:
        lw t0, 0(sp)
        lw t1, 4(sp)
        lw a0, 8(sp)
        lw a1, 12(sp)
        lw a2, 16(sp)
        lw ra, 20(sp)
        addi sp,sp,30
	ret
