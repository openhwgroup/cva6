# See LICENSE for license details.

#*****************************************************************************
# remw.S
#-----------------------------------------------------------------------------
#
# Test remw instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, remw,  2,  20,   6 );
  TEST_RR_OP( 3, remw, -2, -20,   6 );
  TEST_RR_OP( 4, remw,  2,  20,  -6 );
  TEST_RR_OP( 5, remw, -2, -20,  -6 );

  TEST_RR_OP( 6, remw,  0, -1<<31,  1 );
  TEST_RR_OP( 7, remw,  0, -1<<31, -1 );

  TEST_RR_OP( 8, remw, -1<<31, -1<<31, 0 );
  TEST_RR_OP( 9, remw,      1,      1, 0 );
  TEST_RR_OP(10, remw,      0,      0, 0 );
  TEST_RR_OP(11, remw, 0xfffffffffffff897,0xfffffffffffff897, 0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
