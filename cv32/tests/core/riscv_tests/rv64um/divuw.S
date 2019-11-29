# See LICENSE for license details.

#*****************************************************************************
# divuw.S
#-----------------------------------------------------------------------------
#
# Test divuw instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, divuw,         3,  20,   6 );
  TEST_RR_OP( 3, divuw, 715827879, -20 << 32 >> 32,   6 );
  TEST_RR_OP( 4, divuw,         0,  20,  -6 );
  TEST_RR_OP( 5, divuw,         0, -20,  -6 );

  TEST_RR_OP( 6, divuw, -1<<31, -1<<31,  1 );
  TEST_RR_OP( 7, divuw, 0,      -1<<31, -1 );

  TEST_RR_OP( 8, divuw, -1, -1<<31, 0 );
  TEST_RR_OP( 9, divuw, -1,      1, 0 );
  TEST_RR_OP(10, divuw, -1,      0, 0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
