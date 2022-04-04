
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
** Debugger Exception code
*******************************************************************************
*/

#include "corev_uvmt.h"

.section .debugger_exception, "ax"
.global _debugger_exception_start
.global glb_debug_status
.global glb_hart_status
.global glb_debug_exception_status
.global glb_expect_debug_exception
//.global _debugger_fail
//.global _debugger_end
.set test_fail, 0x1

_debugger_exception_start:
	// First check to see if exception was expected
        la a1, glb_expect_debug_exception
	lw t1, 0(a1)
	//beq x0,t1,_debugger_fail
	beq x0,t1,_debugger_exception_fail

	// Set exception status to hart status
        la a1, glb_hart_status
	lw t1, 0(a1)
        la a2, glb_debug_exception_status
        sw t1, 0(a2)

	//j _debugger_end
	j _debugger_exception_end

// Should be exact same function as implmented in debugger.S
	// I can't seem to point to that symble from this file
_debugger_exception_end:
        // Clear debug entry expectation flag
        la a1, glb_expect_debug_entry
        sw x0, 0(a1)
        la a1, glb_expect_debug_exception
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
// Should be exact same function as implmented in debugger.S
_debugger_exception_fail:
        li a0, CV_VP_STATUS_FLAGS_BASE
        li t0, test_fail
        sw t0, 0(a0)
	nop
        nop
        nop
        nop

