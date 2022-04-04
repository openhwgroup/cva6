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

.global _trigger_exit
.global _trigger_test
.global _trigger_code
.global _trigger_test_ebreak
.global _trigger_code_ebreak
.global _trigger_code_illegal_insn
.global _trigger_code_branch_insn
.global _trigger_code_multicycle_insn
.global _trigger_code_cebreak
.type _trigger_code, @function
.type _trigger_code_ebreak, @function
.type _trigger_code_cebreak, @function
.type _trigger_code_illegal_insn, @function
.type _trigger_code_branch_insn, @function
.type _trigger_code_multicycle_insn, @function


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

#    j __trigger_done


     // We will trigger on the _trigger_code addess
	// We should not expect the first instruction to execute
	// The debugger code will move the PC to the trigger_exit_code
	// Which essentially avoid executing all of the code in the trigger_code
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
