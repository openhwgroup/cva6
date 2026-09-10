#include "riscv_test.h"
#include "load_store.h"

RVTEST_CODE_BEGIN
    //Initialize the stack
    la sp, stack

    // Load the first number into register a0
    lx s0, num1

    // Load the second number into register a1
    lx s1, num2

    //Load the result into register a2
    lx a2, result

    //Push the registers to stack
    jal push_pop

    // Add the numbers and store the result in register t2
    add t2, s0, s1

    // Store the result in the memory location reserved for it
    beq t2, a2, success

failure:
    li x1, 1
    j 1f
success:
    li x1, 0
1:
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, t5
1:  j 1b

push_pop:
    cm.push {ra, s0-s1}, - (3 + 1) * xlen_bytes
    nop
    cm.popretz {ra, s0-s1}, (3 + 1) * xlen_bytes
RVTEST_CODE_END

.data
    .align 16
    num1:   xdata 5     // First number
    num2:   xdata 7     // Second number
    result: xdata 12    // Result
    .align 16
    stack:  .space 16 * xlen_bytes

RVTEST_DATA_BEGIN

RVTEST_DATA_END
