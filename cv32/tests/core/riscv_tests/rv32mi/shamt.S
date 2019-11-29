# See LICENSE for license details.

#*****************************************************************************
# csr.S
#-----------------------------------------------------------------------------
#
# Test CSRRx and CSRRxI instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32M
RVTEST_CODE_BEGIN

  # Make sure slli with shamt[4] set is legal.
  TEST_CASE( 2, a0, 65536, li a0, 1; slli a0, a0, 16);

  # Make sure slli with shamt[5] set is not legal.
  TEST_CASE( 3, x0, 1, .word 0x02051513); # slli a0, a0, 32

  TEST_PASSFAIL

.global mtvec_handler
mtvec_handler:
  # Trapping on test 3 is good.
  # Note that since the test didn't complete, TESTNUM is smaller by 1.
  li t0, 2
  bne TESTNUM, t0, fail

  # Make sure CAUSE indicates an illegal instructino.
  csrr t0, mcause
  li t1, CAUSE_ILLEGAL_INSTRUCTION
  bne t0, t1, fail
  j pass

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
