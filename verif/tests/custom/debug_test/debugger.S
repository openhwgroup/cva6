
/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
** Debugger code
*******************************************************************************
*/

#include "corev_uvmt.h"

.section .debugger, "ax"
.global _debugger_start
.global glb_debug_status
.global glb_hart_status
.global glb_expect_debug_entry
.global glb_step_info
.global glb_previous_dpc
.global glb_step_count
.global glb_irq_timeout
.global glb_mcycle_start
.global glb_mcycle_end
.global glb_minstret_start
.global glb_minstret_end
.global _step_trig_point
.global __debugger_stack_start
.global _debugger_fail
.global _debugger_end
.set timer_reg_addr, CV_VP_INTR_TIMER_BASE+0
.set timer_val_addr, CV_VP_INTR_TIMER_BASE+4
.set test_ret_val,   CV_VP_STATUS_FLAGS_BASE
.set test_fail,      0x1

_debugger_start:
        // Debugger Stack
        csrw dscratch, a0       // dscratch0
        la a0, __debugger_stack_start
        //sw t0, 0(a0)
        csrw 0x7b3, t0      	// dscratch1
        sw t1, 4(a0)
        sw t2, 8(a0)
        sw a1, 12(a0)
        sw a2, 16(a0)
        // Check if expecting debug entry
        la a1, glb_expect_debug_entry
        lw t1, 0(a1)
        beq x0,t1,_debugger_fail

        // Read lower 32 bits of mcycle and minstret
        // and store in globals for check at exit
        csrr t1, mcycle
        csrr t2, minstret
        la a1, glb_mcycle_start
        sw t1, 0(a1)
        la a1, glb_minstret_start
        sw t2, 0(a1)

        // Determine Test to execute in debugger code based on glb_hart_status
        la a2, glb_hart_status
        lw t2, 0(a2)

	// ebreak test will loop in debugger code over several iterations
	//  and will increment the global status each time
	li t0,5
	beq t2,t0,_debugger_ebreak // Test 5

	// For all other tests,
	// Set debug status = hart status
    la a1, glb_debug_status
	sw t2, 0(a1)

	li t0, 4
	beq t2,t0,_debugger_simple    // Test 4

	li t0,6
	beq t2,t0,_debugger_csr    // Test 6

    li t0,10
	beq t2,t0,_debugger_ebreak_entry    // Test 10

	li t0,11
	beq t2,t0,_debugger_csr_exception    // Test 11

	li t0,12
	beq t2,t0,_debugger_ecall_exception    // Test 12

	li t0,13
	beq t2,t0,_debugger_mret_call    // Test 13

    li t0,14
    beq t2,t0, _debugger_ebreak_entry // Test 14


    li t0,17
    beq t2,t0, _debugger_wfi_test // Test 17

    li t0,18
    beq t2, t0, _debugger_single_step

    li t0, 19
    beq t2, t0, _debugger_irq

    li t0, 20
    beq t2, t0, _debugger_req_and_irq

    li t0, 21
    beq t2, t0, _debugger_stopcount

    li t0, 22
    beq t2, t0, _debugger_fence

    li t0, 23
    beq t2, t0, _debugger_trigger_disabled_in_debug

    li t0, 24
    beq t2, t0, _debugger_trigger_regs_access

_debugger_trigger_regs_access:
    # R/W trigger regs otherwise not accessed
    # to close coverage holes
    li t0, 0xff
    csrw 0x7a4, t0 # tinfo
    csrr t0, 0x7a4
    li t1, 4
    bne t0, t1, _debugger_fail

    li t0, 0xff
    csrw 0x7a3, t0 # tdata3
    csrr t0, 0x7a3
    bne t0, x0, _debugger_fail

    li t0, 0xff
    csrw 0x7a0, t0 # tsel
    csrr t0, 0x7a0
    bne t0, x0, _debugger_fail

    j _debugger_end


_debugger_fence:
    fence
    nop
    nop
    fence.i
    nop
    nop
    j _debugger_end

_debugger_req_and_irq:
    // Debug was requested at the same cycle as irq
    // Check dpc to see that pc is not at irq handler
    // IRQ used was 30, so addr would be 30*4=120, 0x78
    csrr t0, dpc
    li t1, 0x78
    beq t0, t1, _debugger_fail
    j _debugger_end

_debugger_stopcount:
    li t0, 1<<10
    csrrs x0, dcsr, t0
    j _debugger_end
_debugger_irq:
    // Assert irq
    li a1, timer_reg_addr
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, timer_val_addr
    li t0, 2
    sw t0, 0(a1)

    li t1, 1000
// Wait for 1000 cycles, then timeout
_irq_wait_loop:
    la a1, glb_expect_irq_entry
    lw t0, 0(a1);
    beq t1, x0, _irq_loop_end
    addi t1, t1, -1
    bne t0, x0, _irq_wait_loop
_irq_loop_end:
    la a1, glb_irq_timeout
    sw t1, 0(a1)
    j _debugger_end

_debugger_single_step:
    // Copy step_info
    la a1, glb_step_info
    lw t0, 0(a1)

    // Check action to take
    li t1, 0
    beq t0, t1, _debugger_single_step_basic
    li t1, 1
    beq t0, t1, _debugger_single_step_enable
    li t1, 2
    beq t0, t1, _debugger_single_step_disable
    li t1, 3
    //beq t0, t1, _debugger_single_step_illegal_insn
    beq t0, t1, _debugger_single_step_basic
    li t1, 4
    beq t0, t1, _debugger_single_step_trig_setup
    li t1, 5
    beq t0, t1, _debugger_single_step_stepie_enable
    li t1, 6
    beq t0, t1, _debugger_single_step_stepie_disable
    li t1, 7
    beq t0, t1, _debugger_single_step_cebreak
    li t1, 8
    beq t0, t1, _debugger_single_step_ebreak
    li t1, 9
    beq t0, t1, _debugger_single_step_ebreak_exception
    li t1, 10
    beq t0, t1, _debugger_single_step_cebreak_exception
    j _debugger_fail

_debugger_single_step_stepie_disable:
    // enable stepi
    li t0, 4<<28 | 1<<15 | 1<<2 | 0<<11
    csrw dcsr, t0

    j _debugger_single_step_end
_debugger_single_step_stepie_enable:
    // enable stepi
    li t0, 4<<28 | 1<<15 | 1<<2 | 1<<11
    csrw dcsr, t0

    j _debugger_single_step_end
_debugger_single_step_enable:
     // Check dcsr
    csrr t0, dcsr
    li t1, 4<<28 | 1<<15 | 1<<6 | 3<<0
    bne t0, t1, _debugger_fail

    // Enable step bit in dcsr
    li t0, 4<<28 | 1<<15 | 1<<2
    csrw dcsr, t0

    // ebreak used to enter single step test, incr dpc
    csrr t0, dpc
    addi t0, t0, 2
    csrw dpc, t0
    j _debugger_single_step_end

_debugger_single_step_disable:
    // Turn off single stepping
    li t0, 1<<15
    csrw dcsr, t0
    // Clear glb_expect_debug entry
    // as this will not be done in
    // _debugger_end for single step
    la a1, glb_expect_debug_entry
    sw x0, 0(a1)
    j _debugger_end

_debugger_single_step_trig_setup:
    // Set trigger to match on _step_trig_point
    la t0, _step_trig_point
	csrw tdata2,t0
	li   t1, 1<<2
	csrw tdata1,t1
	li   t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1 <<2
	csrr t2,tdata1
	bne  t1,t2,_debugger_fail
    j _debugger_single_step_basic

_debugger_single_step_end:
    // Store dpc to variable for checking in next step
    la a1, glb_previous_dpc
    csrr t0, dpc
    sw t0, 0(a1)

    // Increase step count
    la a1, glb_step_count
    lw t0, 0(a1)
    addi t0, t0, 1
    sw t0, 0(a1)

    // Clear step info if not 3 (exception) or 5 (irq while stepping)
    // 6, 7 or 8, 9, 10
    // In exception test we expect jumps
    // to mtvec and other places, so keep
    // step info to waive dpc checks
    la a1, glb_step_info
    lw t0, 0(a1)
    li t1, 3
    beq t0, t1, _debugger_end
    li t1, 5
    beq t0, t1, _debugger_end
    li t1, 6
    beq t0, t1, _debugger_end
    li t1, 7
    beq t0, t1, _debugger_end
    li t1, 8
    beq t0, t1, _debugger_end
    li t1, 9
    beq t0, t1, _debugger_end
    li t1, 10
    beq t0, t1, _debugger_end
    li t1, 0
    sw t1, 0(a1)

    // return to m-mode
    j _debugger_end

_debugger_single_step_illegal_insn:
    // Check dcsr
    //            ebreakm   step  stepen
    li t1, 4<<28 | 1<<15 | 4<<6 | 1<<2 | 3<<0
    csrr t2, dcsr
    bne t1, t2, _debugger_fail
    // read dpc and mtvec
    //csrr t0, dpc
    //csrr t1, mtvec
    //andi t1, t1, 0xffffff00
    //bne t0, t1, _debugger_fail
    j _debugger_single_step_end

_debugger_step_trig_entry:
   // Advance dpc to skip first match instruction
    csrr t0, dpc
    la a1, _step_trig_exit
    csrw dpc, a1
    j _debugger_single_step_end

_debugger_single_step_cebreak:
    # If cause == 1, we need to advance dpc by 2
    li t1, 4<<28 | 1<<15 | 1<<6 | 1<<2 | 3<<0
    csrr t2, dcsr
    beq t1, t2, _inc_dpc_cebreak

    j _debugger_single_step_end
_inc_dpc_cebreak:
    csrr t1, dpc
    addi t1, t1, 2
    csrw dpc, t1
    j _debugger_single_step_end

_debugger_single_step_ebreak:
    # If cause == 1, we need to advance dpc by 4
    li t1, 4<<28 | 1<<15 | 1<<6 | 1<<2 | 3<<0
    csrr t2, dcsr
    beq t1, t2, _inc_dpc_ebreak

    j _debugger_single_step_end
_inc_dpc_ebreak:
    csrr t1, dpc
    addi t1, t1, 4
    csrw dpc, t1

    # Turn off dcsr.ebreakm for next two tests
    li t1, 4<<28 | 0<<15 | 1<<6 | 1<<2 | 3<<0
    csrw dcsr, t1
    j _debugger_single_step_end

_debugger_single_step_ebreak_exception:
    j _debugger_single_step_end

_debugger_single_step_cebreak_exception:
    #  depc != 0 => we have passed the first
    # instruction of the handler, and we can
    # set dcsr.ebreakm again
    csrr t0, dpc
    bne t0, x0, _end

    li t1, 4<<28 | 1<<15 | 1<<6 | 1<<2 | 3<<0
    csrw dcsr, t1

_end:
    j _debugger_single_step_end

_debugger_single_step_basic:
    // Check dcsr, jump to match-in-step if flagged in dcsr
    li t1, 4<<28 | 1<<15 | 2<<6 | 1<<2 | 3<<0
    csrr t2, dcsr
    beq t1, t2, _debugger_step_trig_entry


    // Ensure tval (0x343) always == 0
    csrr t1, 0x343
    bne x0, t1, _debugger_fail
//            ebreakm   step  stepen
    li t1, 4<<28 | 1<<15 | 4<<6 | 1<<2 | 3<<0
    bne t1, t2, _debugger_fail
    // Check that dpc increased by 2 or 4
    csrr t0, dpc
    la a1, glb_previous_dpc
    lw t1, 0(a1)
    sub t0, t0, t1
    li t1, 2
    beq t0, t1, _debugger_single_step_end
    li t1, 4
    beq t0, t1, _debugger_single_step_end

    // Waive dpc errors if we expect illegal instruction
    la a1, glb_step_info
    lw t0, 0(a1)
    li t1, 3
//    bne t0, t1, _debugger_fail
    j _debugger_single_step_end

_debugger_csr_exception:
	csrr t2,0xea8 // illegal insn

_debugger_ecall_exception:
	ecall // exception

_debugger_mret_call:
	mret // will invoke debugger exception routine

_debugger_ebreak_entry:
    la a1, glb_debug_status
	li   t1, 4<<28 | 1<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail
        csrr a1,dpc
        addi a1,a1,4 # uncompressed ebreak used to enter debug here
        csrw dpc,a1
        //sw t1, 0(a1)
        j  _debugger_end

_debugger_simple:
    // Check cause 0x3, debugger
    csrr t2,dcsr
    li t1, 4<<28 | 3<<6 | 3<<0
    bne t1, t2, _debugger_fail

	//csrr t2,0xea8 // illegal insn
    li t1, 1
    //sw t1, 0(a1)
    j  _debugger_end

_debugger_csr:
	// Check CSR access
	// When done, set the ebreakm bit to allow next test to enter debug with ebreak

	// TBD BUG FIXME : make sure appropriate list of CSR (from sspecifications)
	//csrr t2,mvendorid
	//csrr t2,marchid
	//csrr t2,mimpid
	csrr t2,mhartid

	// machine trap setup
	csrr t2,mstatus
	csrr t2,misa
	csrr t2,mie
	csrr t2,mtvec
	//FIXME csrr t2,mtval

	// machine trap handling
	csrr t2,mscratch
	csrr t2,mepc
	csrr t2,mcause
	csrr t2,mip

	// -----------------------
	// Debug CSRs

	// Expect DCSR
	//   31:28 XDEBUGER Version = 4
	//    8:6   Cause           = 3 debugger
	//    1:0   Privelege       = 3 Machine
	// TBD FIXME BUG documentation update needed
	li   t1, 4<<28 | 3<<6 | 3<<0
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail
	csrr t2,dpc
	beq  x0,t2,_debugger_fail
	//Already test this csrr t2,dscratch  //dscratch0
	//Already test this csrr t2,0x7b3    //dscratch1

        // Set ebreakm in dcsr
	li   t1, 4<<28 | 3<<6 | 3<<0| 1<<15
	csrw dcsr, t1

	// ----------------------
	// Trigger CSRs

	// Expect TMATCH=TDATA1
	//   31:28 type      = 2
	//      27 dmode     = 1
	//   15:12 action    = 1
	//      6  m(achine) = 1
	li   t1, 2<<28 | 1<<27 | 1<<12 | 1<<6
	csrr t2,tdata1
	bne  t1,t2,_debugger_fail
	csrr t2,tselect
	bne  x0,t2,_debugger_fail
	csrr t2,tdata2
	bne  x0,t2,_debugger_fail
	csrr t2,tdata3
	bne  x0,t2,_debugger_fail

	j _debugger_end

_debugger_ebreak:
    li t0, 4<<28 | 3<<6 | 3<<0
    csrr t1, dcsr
    bne t0, t1, _debugger_fail
        // Increment glb_debug_status
        la a1, glb_debug_status
        lw t1, 0(a1)
        addi t1,t1,1
        sw t1, 0(a1)
	// Repeat executing debug code until debug status = hart_status + 3
	addi t0, t2, 3
	beq  t1, t0, _debugger_end
    // Execute non-compressed ebreak for iteration 2
    addi t0, t2, 2
    beq t1, t0, _uncompressed_ebreak
	// Debugger Un-Stack and call debugger code from start using ebreak
    csrr t0, 0x7b3
	lw   t1, 4(a0)
        lw   t2, 8(a0)
        lw   a1, 12(a0)
        lw   a2, 16(a0)
        csrr a0, dscratch
        ebreak
_uncompressed_ebreak:
	// Debugger Un-Stack and call debugger code from start using ebreak
    csrr t0, 0x7b3
	lw   t1, 4(a0)
        lw   t2, 8(a0)
        lw   a1, 12(a0)
        lw   a2, 16(a0)
        csrr a0, dscratch
        .4byte 0x00100073 # ebreak

_debugger_trigger_in_debug:
    // setup address to trigger on
	la   a1, _debugger_trig_point
	csrw tdata2,a1
	li   t1, 1<<2
	csrw tdata1,t1
	li   t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1 <<2
	csrr t2,tdata1
	bne  t1,t2,_debugger_fail

    // Clear glb_expect_debug_entry
    // If we trig, we'll reenter debug and
    // test will fail due to 0 flag
    la a1, glb_expect_debug_entry
    li t1, 0
    sw t1, 0(a1)
_debugger_trig_point:
    // Should _not_trig here
    nop
    // Clear trigger
    li t1, 0<<2
    csrw tdata1, t1
    j _debugger_end

_debugger_trigger_disabled_in_debug:
    // setup address to trigger on
	la   a1, _debugger_trig_point_dis
    // Set trig enable to 0
	csrw tdata2,a1
	li   t1, 0<<2
	csrw tdata1,t1
	li   t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 0 <<2
	csrr t2,tdata1
	bne  t1,t2,_debugger_fail

    // Clear glb_expect_debug_entry
    // If we trig, we'll reenter debug and
    // test will fail due to 0 flag
    la a1, glb_expect_debug_entry
    li t1, 0
    sw t1, 0(a1)
_debugger_trig_point_dis:
    // Should _not_trig here
    nop
    // Clear trigger
    li t1, 0<<2
    csrw tdata1, t1
    j _debugger_end
_debugger_wfi_test:
    la a1, glb_debug_status
    csrr t2,dcsr
    // ebreakm is set by previous test
    li t1, 4<<28 | 3<<6 | 3<<0 | 1<<15
    bne t1, t2, _debugger_fail

    // If the following wfi is not converted
    // to a nop, test will hang
    wfi
    j  _debugger_end

_debugger_end:
    // Check counter values.
    csrr t1, mcycle
    la a1, glb_mcycle_start
    lw t2, 0(a1)
    sub t1, t1, t2
    beq t1, x0, _debugger_fail

    csrr t1, minstret
    la a1, glb_minstret_start
    lw t2, 0(a1)
    sub t1, t1, t2
    beq t1, x0, _debugger_fail

    // If single stepping, do not clear
    la a1, glb_hart_status
    lw t0, 0(a1)
    li t1, 18
    beq t0, t1, _debugger_end_continue

    // Clear debug entry expectation flag
    la a1, glb_expect_debug_entry
    sw x0, 0(a1)
_debugger_end_continue:
        // Debugger Un-Stack
        //lw t0, 0(a0)
        la a0, __debugger_stack_start
        csrr t0, 0x7b3
        lw   t1, 4(a0)
        lw   t2, 8(a0)
        lw   a1, 12(a0)
        lw   a2, 16(a0)
        csrr a0, dscratch
        dret
_debugger_fail: //Test Failed
        li a0, CV_VP_STATUS_FLAGS_BASE
        li t0, test_fail
        sw t0, 0(a0)
	nop
        nop
        nop
        nop

