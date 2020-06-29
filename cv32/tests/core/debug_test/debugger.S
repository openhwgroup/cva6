
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

.section .debugger, "ax"
.global _debugger_start
.global glb_debug_status
.global glb_hart_status
.global glb_expect_debug_entry
.global __debugger_stack_start
.global _debugger_fail
.global _debugger_end
.set test_ret_val, 0x20000000
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

	li t0,7
	beq t2,t0,_debugger_trigger_setup    // Test 7

	li t0,8
	beq t2,t0,_debugger_trigger_match    // Test 8

	li t0,9
	beq t2,t0,_debugger_trigger_disable    // Test 9

	li t0,10
	beq t2,t0,_debugger_ebreak_entry    // Test 10

	li t0,11
	beq t2,t0,_debugger_csr_exception    // Test 11

	li t0,12
	beq t2,t0,_debugger_ecall_exception    // Test 12

	li t0,13
	beq t2,t0,_debugger_mret_call    // Test 13

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
        addi a1,a1,2
        csrw dpc,a1
        //sw t1, 0(a1)
        j  _debugger_end

_debugger_simple:
        la a1, glb_debug_status
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
	csrr t2,0x7a8 //mcontext
	bne  x0,t2,_debugger_fail
	csrr t2,0x7aa //scontext
	bne  x0,t2,_debugger_fail

	j _debugger_end
_debugger_trigger_setup:
	// setup address to trigger on
	la   a1,_trigger_code
	csrw tdata2,a1
	li   t1, 1<<2
	csrw tdata1,t1
	li   t1, 2<<28 | 1<<27 | 1<<12 | 1<<6 | 1 <<2
	csrr t2,tdata1
	bne  t1,t2,_debugger_fail
	j    _debugger_end
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
	j   _debugger_end
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

_debugger_ebreak:
        // Increment glb_debug_status
        la a1, glb_debug_status
        lw t1, 0(a1)
        addi t1,t1,1
        sw t1, 0(a1)
	// Repeat executing debug code until debug status = hart_status + 3
	addi t0, t2, 3
	beq  t1, t0, _debugger_end
	// Debugger Un-Stack and call debugger code from start using ebreak
        csrr t0, 0x7b3
	lw   t1, 4(a0)
        lw   t2, 8(a0)
        lw   a1, 12(a0)
        lw   a2, 16(a0)
        csrr a0, dscratch
        ebreak
_debugger_end:	
        // Clear debug entry expectation flag
        la a1, glb_expect_debug_entry
        sw x0, 0(a1)
        // Debugger Un-Stack
        //lw t0, 0(a0)
        csrr t0, 0x7b3
        lw   t1, 4(a0)
        lw   t2, 8(a0)
        lw   a1, 12(a0)
        lw   a2, 16(a0)
        csrr a0, dscratch
        dret
_debugger_fail: //Test Failed
        li a0, test_ret_val
        li t0, test_fail
        sw t0, 0(a0)
	nop
        nop
        nop
        nop
        
