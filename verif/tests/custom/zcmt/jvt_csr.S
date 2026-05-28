#include "riscv_test.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

	la t0, trap_handler
	csrw mtvec, t0
    la t0, __jvt_base$

    csrw  jvt, t0
    fence.i    
    csrr x7, jvt

    j success


trap_handler:
	lui    t0, %hi(failure)        # Load upper 20 bits of target address into t0
    addi   t0, t0, %lo(failure)    # Add the lower 12 bits to t0
    jalr   x0, 0(t0) 

// jump to this label to signal that the test failed
failure:
    li x1, 1
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, t5
	self_loop_2: j self_loop_2

// jump to this label to signal that the test passed
success:
    li x1, 0
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, t5
	self_loop: j self_loop

RVTEST_CODE_END

.data

RVTEST_DATA_BEGIN

// Jump Vector Table (JVT) Section
.section .riscv.jvt, "ax"
.align 6
__jvt_base$:
    .word 0x80000054
    .word 0x80000800
    .word 0x80000802
    .word 0x80000804


RVTEST_DATA_END