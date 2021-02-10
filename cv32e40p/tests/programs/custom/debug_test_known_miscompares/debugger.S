
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


	// For all other tests,
	// Set debug status = hart status
    la a1, glb_debug_status
	sw t2, 0(a1)
    
    li t0, 1
    beq t2, t0, _debugger_illegal_and_req
    li t0, 2
    beq t2, t0, _debugger_single_step_enable
    li t0, 3
    beq t2, t0, _debugger_single_step_ebreak
    li t0, 4
    beq t2, t0, _debugger_single_step_disable

    j _debugger_fail

_debugger_single_step_ebreak:
    j _debugger_end

_debugger_single_step_enable:
    // Enable step bit in dcsr
    li t0, 4<<28 | 0<<15 | 1<<2 
    csrw dcsr, t0
    j _debugger_end

_debugger_single_step_disable:
    li t0, 4<<28 | 0<<15 | 0<<2 
    csrw dcsr, t0
    j _debugger_end

_debugger_illegal_and_req:
    # Test expects entry of exception handler
    # to be stored in dpc.
    csrr t0, dpc
    bne t0, x0, _debugger_fail

    j _debugger_end


_debugger_end:
    
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
        li a0, test_ret_val
        li t0, test_fail
        sw t0, 0(a0)
	nop
        nop
        nop
        nop
        
