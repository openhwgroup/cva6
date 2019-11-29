# See LICENSE for license details.

#*****************************************************************************
# divw.S
#-----------------------------------------------------------------------------
#
# Test divw instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, divw,  3,  20,   6 );
  TEST_RR_OP( 3, divw, -3, -20,   6 );
  TEST_RR_OP( 4, divw, -3,  20,  -6 );
  TEST_RR_OP( 5, divw,  3, -20,  -6 );

  TEST_RR_OP( 6, divw, -1<<31, -1<<31,  1 );
  TEST_RR_OP( 7, divw, -1<<31, -1<<31, -1 );

  TEST_RR_OP( 8, divw, -1, -1<<31, 0 );
  TEST_RR_OP( 9, divw, -1,      1, 0 );
  TEST_RR_OP(10, divw, -1,      0, 0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
