#include "riscv_test.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN
    
    li s1, 5
    li s2, 7
    cm.mva01s s1, s2
    
    bne a0, s1, failure
    beq a1, s2, success
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
