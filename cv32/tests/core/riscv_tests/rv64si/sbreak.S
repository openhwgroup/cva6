# See LICENSE for license details.

#*****************************************************************************
# scall.S
#-----------------------------------------------------------------------------
#
# Test syscall trap.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64S
RVTEST_CODE_BEGIN

#ifdef __MACHINE_MODE
  #define sscratch mscratch
  #define sstatus mstatus
  #define scause mcause
  #define sepc mepc
  #define sret mret
  #define stvec_handler mtvec_handler
#endif

  li TESTNUM, 2

do_break:
  sbreak
  j fail

  TEST_PASSFAIL

  .align 2
  .global stvec_handler
stvec_handler:
  li t1, CAUSE_BREAKPOINT
  csrr t0, scause
  bne t0, t1, fail
  la t1, do_break
  csrr t0, sepc
  bne t0, t1, fail
  j pass

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
