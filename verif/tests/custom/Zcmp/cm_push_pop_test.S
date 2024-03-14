#include "riscv_test.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN
    //Initialize the stack
    la sp, stack

    // Load the first number into register a0
    lw s0, num1
    
    // Load the second number into register a1
    lw s1, num2
    
    //Load the result into register a2
    lw a2, result

    //Two consecutive move instructions replaced by the compressed move instruction
    //mv s0, a0
    //mv s1, a1

    //Push the registers to stack
    jal push_pop

    // Add the numbers and store the result in register t2
    add t2, s0, s1
    
    // Store the result in the memory location reserved for it
    beq t2, a2, success
failure:
    li x1, 1
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, t5
	self_loop_2: j self_loop_2
    
success:
    li x1, 0
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, t5
	self_loop: j self_loop

push_pop:
    cm.push {ra, s0-s1}, -16
    nop
    cm.pop {ra, s0-s1}, 16
    jr ra

RVTEST_CODE_END

.data
    num1:   .word 5      // First number
    num2:   .word 7      // Second number
    result: .word 12      // Result
    stack:  .space 100
    
RVTEST_DATA_BEGIN

RVTEST_DATA_END
