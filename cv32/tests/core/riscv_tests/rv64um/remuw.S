# See LICENSE for license details.

#*****************************************************************************
# remuw.S
#-----------------------------------------------------------------------------
#
# Test remuw instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, remuw,   2,  20,   6 );
  TEST_RR_OP( 3, remuw,   2, -20,   6 );
  TEST_RR_OP( 4, remuw,  20,  20,  -6 );
  TEST_RR_OP( 5, remuw, -20, -20,  -6 );

  TEST_RR_OP( 6, remuw,      0, -1<<31,  1 );
  TEST_RR_OP( 7, remuw, -1<<31, -1<<31, -1 );

  TEST_RR_OP( 8, remuw, -1<<31, -1<<31, 0 );
  TEST_RR_OP( 9, remuw,      1,      1, 0 );
  TEST_RR_OP(10, remuw,      0,      0, 0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
