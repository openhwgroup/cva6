#include "riscv_test.h"
#include "load_store.h"

RVTEST_CODE_BEGIN
    //Initialize the stack
    la sp, stack

    jal push_pop_1
    // If ra is not poped correctly we're anyway going wild

    // Load the first number into register s0
    lx s0, num1

    // Load the second number into register s1
    lx s1, num2

    // Load the third number into register s2
    lx s2, num3

    //Push the registers to stack
    jal push_pop_3

    //Load the result into register a2
    lx a2, result_3

    // Add the numbers and store the result in register t2
    add t2, s0, s1
    add t2, t2, s2

    // Check that we retrieved the correct values
    bne t2, a2, failure

    // Load the values to check with
    lx s3, num4
    lx s4, num5
    lx s5, num6
    lx s6, num7
    lx s7, num8
    lx s8, num9
    lx s9, num10
    //Push the registers to stack
    jal push_pop_10
    //Load the result into register a2
    lx a2, result_10
    // Add the numbers and store the result in register t2
    add t2, s0, s1
    add t2, t2, s2
    add t2, t2, s3
    add t2, t2, s4
    add t2, t2, s5
    add t2, t2, s6
    add t2, t2, s7
    add t2, t2, s8
    add t2, t2, s9
    // Check that we retrieved the correct values
    bne t2, a2, failure

    lx s10, num11
    lx s11, num12
    //Push the registers to stack
    jal push_pop_all
    //Load the result into register a2
    lx a2, result_all
    // Add the numbers and store the result in register t2
    add t2, s0, s1
    add t2, t2, s2
    add t2, t2, s3
    add t2, t2, s4
    add t2, t2, s5
    add t2, t2, s6
    add t2, t2, s7
    add t2, t2, s8
    add t2, t2, s9
    add t2, t2, s10
    add t2, t2, s11
    // Check that we retrieved the correct values
    bne t2, a2, failure
    jal push_pop_check_frame
    j success

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

push_pop_1:
    cm.push {ra}, -align_16up(1 * xlen_bytes)
    c.nop
    cm.pop {ra}, align_16up(1 * xlen_bytes)
    jr ra

    // For a reason I can't explain, this seems necessary, although unrelated
    // to zcmp
    .align 2
push_pop_3:
    cm.push {ra, s0-s2}, -align_16up((1 + 3) * xlen_bytes)
    c.nop
    cm.pop {ra, s0-s2}, align_16up((1 + 3) * xlen_bytes)
    jr ra

push_pop_10:
    cm.push {ra, s0-s9}, -align_16up((1 + 10) * xlen_bytes)
    c.nop
    cm.pop {ra, s0-s9}, align_16up((1 + 10) * xlen_bytes)
    jr ra

push_pop_all:
    cm.push {ra, s0-s11}, -align_16up((1 + 15) * xlen_bytes)
    c.nop
    cm.pop {ra, s0-s11}, align_16up((1 + 15) * xlen_bytes)
    jr ra

push_pop_check_frame:
    mv a0, sp
    cm.push  {ra, s0-s5}, -align_16up((7 + 1) * xlen_bytes)
    lx  t1, -7 * xlen_bytes(a0)
    bne t1, ra, failure
    lx  t1, -6 * xlen_bytes(a0)
    bne t1, s0, failure
    lx  t1, -5 * xlen_bytes(a0)
    bne t1, s1, failure
    lx  t1, -4 * xlen_bytes(a0)
    bne t1, s2, failure
    lx  t1, -3 * xlen_bytes(a0)
    bne t1, s3, failure
    lx  t1, -2 * xlen_bytes(a0)
    bne t1, s4, failure
    lx  t1, -1 * xlen_bytes(a0)
    bne t1, s5, failure
    // Last slot(s) are 16-byte padding
    cm.pop  {ra, s0-s5}, align_16up((7 + 1) * xlen_bytes)
    jr  ra

RVTEST_CODE_END

.data
    .align 16
    num1:       xdata 1   // First number
    num2:       xdata 2   // Second number
    num3:       xdata 3
    result_3:   xdata 6   // Result
    num4:       xdata 4
    num5:       xdata 5
    num6:       xdata 6
    num7:       xdata 7
    num8:       xdata 8
    num9:       xdata 9
    num10:      xdata 10
    result_10:  xdata 55
    num11:      xdata 11
    num12:      xdata 12
    result_all: xdata 78
    .align 16
    stack:  .space 32 * xlen_bytes

RVTEST_DATA_BEGIN

RVTEST_DATA_END
