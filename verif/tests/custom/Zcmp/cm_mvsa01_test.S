#include "riscv_test.h"
#include "load_store.h"

RVTEST_CODE_BEGIN

    li a0, 5
    li a1, 7
    cm.mvsa01 s1, s2

    bne a0, s1, failure
    beq a1, s2, success

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

RVTEST_CODE_END

.data

RVTEST_DATA_BEGIN

RVTEST_DATA_END
