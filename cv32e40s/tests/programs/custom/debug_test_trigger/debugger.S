
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
.global glb_mcycle_start
.global glb_mcycle_end
.global glb_minstret_start
.global glb_minstret_end
.global _trigger_code
.global _trigger_code_ebreak
.global _trigger_code_cebreak
.global _trigger_code_illegal_insn
.global _trigger_code_branch_insn
.global _trigger_code_multicycle_insn
.global __debugger_stack_start
.global _debugger_fail
.global _debugger_end
.set test_fail, 0x1

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


	// For all other tests,
	// Set debug status = hart status
    la a1, glb_debug_status
	sw t2, 0(a1)


	li t0,7
	beq t2,t0,_debugger_trigger_setup    // Test 7

    li t0,10
    beq t2,t0, _debugger_trigger_match_no_dpc // Test 10

	li t0,8
	beq t2,t0,_debugger_trigger_match    // Test 8

    li t0, 81
    beq t2,t0, _debugger_trigger_match_ebreak

    li t0, 82
    beq t2, t0, _debugger_trigger_match_cebreak

    li t0, 83
    beq t2, t0, _debugger_trigger_match_illegal_insn

    li t0, 84
    beq t2, t0, _debugger_trigger_match_branch_insn

    li t0, 85
    beq t2, t0, _debugger_trigger_match_multicycle_insn

	li t0,9
	beq t2,t0, _debugger_trigger_disable    // Test 9

	li t0,13
	beq t2,t0, _debugger_mret_call    // Test 13

    li t0,15
    beq t2,t0, _debugger_trigger_in_debug // Test 15


_debugger_mret_call:
	mret // will invoke debugger exception routine

_debugger_trigger_setup:
	// setup address to trigger on
	la   a1,_trigger_code
	csrw tdata2,a1
	li   t1, 1<<2
	csrw tdata1,t1
	li   t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1 <<2
	csrr t2,tdata1
	bne  t1,t2,_debugger_fail

   	li   t1, 4<<28 | 2<<6 | 3<<0 | 1<<15
    csrw dcsr, t1
	j    _debugger_end

_debugger_trigger_match_no_dpc:
	// Expect DCSR
	//   31:28 XDEBUGER Version = 4
	//    8:6   Cause           = 2 Trigger
	//    1:0   Privelege       = 3 Machine
	// TBD FIXME BUG documentation update needed
	li   t1, 4<<28 | 2<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail

    // Clear the tdata1 execute field (tdata1[2]) to avoid re-entering the trigger when dret executes
    csrci tdata1, 0x4

    j _debugger_end

_debugger_trigger_match:
	// Expect DCSR
	//   31:28 XDEBUGER Version = 4
	//    8:6   Cause           = 2 Trigger
	//    1:0   Privelege       = 3 Machine
	// TBD FIXME BUG documentation update needed
	li   t1, 4<<28 | 2<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail

	la   a1,_trigger_code
	csrr a2,dpc
	bne  a1,a2,_debugger_fail
	la   a1,_trigger_exit
	csrw dpc,a1

    // Setup match addr for next match: ebreak
    la a1, _trigger_code_ebreak
    csrw tdata2, a1
	j   _debugger_end
_debugger_trigger_match_ebreak:
	// Expect DCSR
	//   31:28 XDEBUGER Version = 4
	//    8:6   Cause           = 2 Trigger
	//    1:0   Privelege       = 3 Machine
	// TBD FIXME BUG documentation update needed
	li   t1, 4<<28 | 2<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail

	la   a1,_trigger_code_ebreak
	csrr a2,dpc
	bne  a1,a2,_debugger_fail

    # Advance pc past ebreak insn
    addi a2, a2, 4
    csrw dpc, a2

    # Setup match addr for next match: c.ebreak
    la a1, _trigger_code_cebreak
    csrw tdata2, a1

	j   _debugger_end
_debugger_trigger_match_cebreak:
	// Expect DCSR
	//   31:28 XDEBUGER Version = 4
	//    8:6   Cause           = 2 Trigger
	//    1:0   Privelege       = 3 Machine
	// TBD FIXME BUG documentation update needed
	li   t1, 4<<28 | 2<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail

	la   a1,_trigger_code_cebreak
	csrr a2,dpc
	bne  a1,a2,_debugger_fail

    # Advance pc past c.ebreak insn
    addi a2, a2, 2
    csrw dpc, a2

    # Setup match addr for next match: illegal_insn
    la a1, _trigger_code_illegal_insn
    csrw tdata2, a1

    // Disable trigger
    //csrw tdata1, x0
	j   _debugger_end

_debugger_trigger_match_illegal_insn:
   	li   t1, 4<<28 | 2<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail

	la   a1,_trigger_code_illegal_insn
	csrr a2,dpc
	bne  a1,a2,_debugger_fail

    # Advance pc past illegal insn (dret, 4 bytes)
    addi a2, a2, 4
    csrw dpc, a2

    # Setup match addr for next match: branch_insn
    la a1, _trigger_code_branch_insn
    csrw tdata2, a1

    j _debugger_end

_debugger_trigger_match_branch_insn:
   	li   t1, 4<<28 | 2<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail

	la   a1,_trigger_code_branch_insn
	csrr a2,dpc
	bne  a1,a2,_debugger_fail

    # Advance pc past illegal branch (beq, 4 bytes)
    addi a2, a2, 4
    csrw dpc, a2

    # Setup match addr for next match: multicycle_insn
    la a1, _trigger_code_multicycle_insn
    csrw tdata2, a1

    j _debugger_end

_debugger_trigger_match_multicycle_insn:
   	li   t1, 4<<28 | 2<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail

	la   a1,_trigger_code_multicycle_insn
	csrr a2,dpc
	bne  a1,a2,_debugger_fail

    # Advance pc past multicycle insn (mulhsu, 4 bytes)
    addi a2, a2, 4
    csrw dpc, a2

    # disable trigger
    csrw tdata1, x0

    j _debugger_end

_debugger_trigger_disable:
	// Expect DCSR
	//   31:28 XDEBUGER Version = 4
	//    8:6   Cause           = 3 debugger
	//    1:0   Privelege       = 3 Machine
	// TBD FIXME BUG documentation update needed
	li   t1, 4<<28 | 3<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail

	csrw tdata1,x0
	li   t1, 2<<28 | 1<<27 | 1<<12 | 1<<6
	csrr t2,tdata1
	bne  t1,t2,_debugger_fail
	j    _debugger_end


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

_debugger_end:
    // Check counter values. They should have increased while in debug
    // regardless of stopcount bit in csr
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

