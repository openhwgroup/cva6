# See LICENSE for license details.

#*****************************************************************************
# divu.S
#-----------------------------------------------------------------------------
#
# Test divu instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, divu,                   3,  20,   6 );
  TEST_RR_OP( 3, divu, 3074457345618258599, -20,   6 );
  TEST_RR_OP( 4, divu,                   0,  20,  -6 );
  TEST_RR_OP( 5, divu,                   0, -20,  -6 );

  TEST_RR_OP( 6, divu, -1<<63, -1<<63,  1 );
  TEST_RR_OP( 7, divu,     0,  -1<<63, -1 );

  TEST_RR_OP( 8, divu, -1, -1<<63, 0 );
  TEST_RR_OP( 9, divu, -1,      1, 0 );
  TEST_RR_OP(10, divu, -1,      0, 0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
