#include "riscv_test.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

    li s1, 9
    .2byte 0xace6    # cm.mva01s s1, s1

    bne a0, s1, failure
    bne a1, s1, failure

    j success
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

RVTEST_CODE_END

.data

RVTEST_DATA_BEGIN

RVTEST_DATA_END
