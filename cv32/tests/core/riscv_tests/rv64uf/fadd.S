# See LICENSE for license details.

#*****************************************************************************
# fadd.S
#-----------------------------------------------------------------------------
#
# Test f{add|sub|mul}.s instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_FP_OP2_S( 2,  fadd.s, 0,                3.5,        2.5,        1.0 );
  TEST_FP_OP2_S( 3,  fadd.s, 1,              -1234,    -1235.1,        1.1 );
  TEST_FP_OP2_S( 4,  fadd.s, 1,         3.14159265, 3.14159265, 0.00000001 );

  TEST_FP_OP2_S( 5,  fsub.s, 0,                1.5,        2.5,        1.0 );
  TEST_FP_OP2_S( 6,  fsub.s, 1,              -1234,    -1235.1,       -1.1 );
  TEST_FP_OP2_S( 7,  fsub.s, 1,         3.14159265, 3.14159265, 0.00000001 );

  TEST_FP_OP2_S( 8,  fmul.s, 0,                2.5,        2.5,        1.0 );
  TEST_FP_OP2_S( 9,  fmul.s, 1,            1358.61,    -1235.1,       -1.1 );
  TEST_FP_OP2_S(10,  fmul.s, 1,      3.14159265e-8, 3.14159265, 0.00000001 );

  # Is the canonical NaN generated for Inf - Inf?
  TEST_FP_OP2_S(11,  fsub.s, 0x10, qNaNf, Inf, Inf);

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
