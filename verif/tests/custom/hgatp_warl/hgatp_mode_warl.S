#include "riscv_test.h"
#include "test_macros.h"

.option arch, +h

#define CSR_HGATP               0x680
#define HGATP_MODE_SV39X4       8
#define HGATP_MODE_UNSUPPORTED  1

RVTEST_RV64M
RVTEST_CODE_BEGIN

  li TESTNUM, 1

  # Install an initial legal value:
  # MODE = Sv39x4
  # PPN  = 0x100
  li   t0, HGATP_MODE_SV39X4
  slli t0, t0, 60
  ori  t0, t0, 0x100

  csrw CSR_HGATP, t0
  csrr t1, CSR_HGATP

  bne  t1, t0, fail

  li TESTNUM, 2

  # Write an unsupported MODE with a different PPN.
  # MODE must be legalized, but PPN must still update.
  li   t2, HGATP_MODE_UNSUPPORTED
  slli t2, t2, 60
  ori  t2, t2, 0x200

  csrw CSR_HGATP, t2
  csrr t3, CSR_HGATP

  # Expected:
  # MODE remains Sv39x4
  # PPN changes to 0x200
  li   t4, HGATP_MODE_SV39X4
  slli t4, t4, 60
  ori  t4, t4, 0x200

  bne  t3, t4, fail

  j pass

  TEST_PASSFAIL

RVTEST_CODE_END

RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
