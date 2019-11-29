# See LICENSE for license details.

#*****************************************************************************
# fcmp.S
#-----------------------------------------------------------------------------
#
# Test f{eq|lt|le}.d instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

#if __riscv_xlen == 32
    # Replace the function with the 32-bit variant defined in test_macros.h
    #undef TEST_FP_CMP_OP_D
    #define TEST_FP_CMP_OP_D TEST_FP_CMP_OP_D32
#endif

  TEST_FP_CMP_OP_D( 2, feq.d, 0x00, 1, -1.36, -1.36)
  TEST_FP_CMP_OP_D( 3, fle.d, 0x00, 1, -1.36, -1.36)
  TEST_FP_CMP_OP_D( 4, flt.d, 0x00, 0, -1.36, -1.36)

  TEST_FP_CMP_OP_D( 5, feq.d, 0x00, 0, -1.37, -1.36)
  TEST_FP_CMP_OP_D( 6, fle.d, 0x00, 1, -1.37, -1.36)
  TEST_FP_CMP_OP_D( 7, flt.d, 0x00, 1, -1.37, -1.36)

  # Only sNaN should signal invalid for feq.
  TEST_FP_CMP_OP_D( 8, feq.d, 0x00, 0, NaN, 0)
  TEST_FP_CMP_OP_D( 9, feq.d, 0x00, 0, NaN, NaN)
  TEST_FP_CMP_OP_D(10, feq.d, 0x10, 0, sNaN, 0)

  # qNaN should signal invalid for fle/flt.
  TEST_FP_CMP_OP_D(11, flt.d, 0x10, 0, NaN, 0)
  TEST_FP_CMP_OP_D(12, flt.d, 0x10, 0, NaN, NaN)
  TEST_FP_CMP_OP_D(13, flt.d, 0x10, 0, sNaN, 0)
  TEST_FP_CMP_OP_D(14, fle.d, 0x10, 0, NaN, 0)
  TEST_FP_CMP_OP_D(15, fle.d, 0x10, 0, NaN, NaN)
  TEST_FP_CMP_OP_D(16, fle.d, 0x10, 0, sNaN, 0)

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
