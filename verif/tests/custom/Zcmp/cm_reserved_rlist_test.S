#include "riscv_test.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

    # Count the number of expected illegal-instruction traps.
    li s0, 0

    # Zcmp reserves rlist values 0 through 3 for the
    # cm.push/cm.pop/cm.popretz/cm.popret instruction families.
    #
    # rlist occupies bits [7:4].
    # spimm is kept at zero because this test targets rlist legality.

    # cm.push, rlist = 0..3
    .2byte 0xb802
    .2byte 0xb812
    .2byte 0xb822
    .2byte 0xb832

    # cm.pop, rlist = 0..3
    .2byte 0xba02
    .2byte 0xba12
    .2byte 0xba22
    .2byte 0xba32

    # cm.popretz, rlist = 0..3
    .2byte 0xbc02
    .2byte 0xbc12
    .2byte 0xbc22
    .2byte 0xbc32

    # cm.popret, rlist = 0..3
    .2byte 0xbe02
    .2byte 0xbe12
    .2byte 0xbe22
    .2byte 0xbe32

    # Every reserved instruction above must have trapped.
    li t0, 16
    bne s0, t0, failure

    RVTEST_PASS

failure:
    li TESTNUM, 1
    RVTEST_FAIL

mtvec_handler:
    # Only illegal-instruction exceptions are expected.
    csrr t0, mcause
    li t1, CAUSE_ILLEGAL_INSTRUCTION
    bne t0, t1, failure

    # Record this expected trap.
    addi s0, s0, 1

    # Every injected instruction is a 16-bit compressed instruction.
    # Advance mepc so execution continues at the following encoding.
    csrr t0, mepc
    addi t0, t0, 2
    csrw mepc, t0

    mret

RVTEST_CODE_END

.data

RVTEST_DATA_BEGIN

RVTEST_DATA_END
