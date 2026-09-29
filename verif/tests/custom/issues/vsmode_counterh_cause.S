# vsmode_counterh_cause.S
# Directed test for openhwgroup/cva6#3466:
# "RV64+H: high-half counter CSR access from VS-mode reports cause 22
# instead of cause 2"
#
# Per spec, on RV64 (XLEN=64) an access to a high-half counter CSR (cycleh,
# instreth, hpmcounterNh) is always illegal (cause 2), regardless of mode or
# counter-enable bits -- high-half CSRs only exist on RV32. CVA6 currently
# gates cycleh/instreth using the same counter-enable privilege logic as the
# low CSRs, with no RV64 guard, so from VS-mode with mcounteren enabled but
# hcounteren disabled, the access instead raises a virtual-instruction
# exception (cause 22) via virtual_privilege_violation.
#
# This test: from M-mode, enables mcounteren bit0 (cycle/cycleh), leaves
# hcounteren bit0 clear (default), enters VS-mode via mret (mstatus.MPP=S, mstatus.MPV=1),
# and executes a cycleh read. The resulting trap (delivered
# to M-mode, no H-delegation configured) must report mcause=2, not 22.

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  .align 2
  .option norvc

  li TESTNUM, 2

  la t0, mtvec_handler
  csrw mtvec, t0

  # enable mcounteren bit0 (cycle/cycleh gating) -- leaves hcounteren bit0
  # clear (its reset value), so accessing from V=1,S-mode should hit the
  # virtual_privilege_violation path in the buggy RTL.
  li t0, 1
  csrs mcounteren, t0

  # mstatus.MPP = S (2'b01, bits [12:11]) and mstatus.MPV = 1 (bit 39) --
  # MRET (unlike SRET, which uses hstatus.SPV) uses mstatus.MPV to decide
  # the new virtualization mode, so it lands in VS-mode (S-mode, V=1).
  csrr t0, mstatus
  li t1, ~(3 << 11)
  and t0, t0, t1
  li t1, (1 << 11)
  or t0, t0, t1
  li t1, 1
  slli t1, t1, 39
  or t0, t0, t1
  csrw mstatus, t0

  la t0, vs_mode_entry
  csrw mepc, t0
  mret

vs_mode_entry:
  csrr t0, 0xC80                    # cycleh -- must trap, cause must be 2

  # should never retire past the csrr above
  j fail

  TEST_PASSFAIL

  .align 8
  .global mtvec_handler
mtvec_handler:
  csrr t0, mcause
  li t1, 2
  beq t0, t1, 1f
  j fail
1:
  j pass

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
