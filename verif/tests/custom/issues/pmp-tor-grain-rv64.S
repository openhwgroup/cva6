# Regression test for CVA6 issue #3342.
#
# CVA6 implements an eight-byte PMP grain (G=1), so pmpaddr[0] must not
# affect either boundary of a TOR region. Check a denied partial boundary,
# an allowed complete doubleword, and a lower boundary shared by two entries.

#include "encoding.h"

  .equ MSTATUS_MPP_S,          (PRV_S << 11)
  .equ CAUSE_LOAD_ACCESS_FAULT, 5
  .equ PMP_RWX_TOR,            (PMP_TOR | PMP_R | PMP_W | PMP_X)
  .equ PMP_X_TOR,              (PMP_TOR | PMP_X)
  .equ PMP_RW_TOR,             (PMP_TOR | PMP_R | PMP_W)
  .equ SECRET,                 0x89abcdef01234567

  # Keep this complete test in the first load segment. This makes the PMP
  # regression independent of ELF segment preloading in the test harness.
  .section .text.init, "ax", @progbits
  .align 2
  .globl main

main:
  la      t0, trap_handler
  csrw    mtvec, t0
  csrw    medeleg, zero
  csrw    mideleg, zero
  csrw    satp, zero
  sfence.vma

  li      t0, 1
  csrw    mscratch, t0
  j       setup_partial_top

# Phase 1: pmpaddr0 contains (target + 4) >> 2. Its low bit must be ignored,
# so the effective top is target and an S-mode load at target must fault.
setup_partial_top:
  csrw    pmpcfg0, zero

  la      t0, target
  addi    t0, t0, 4
  srli    t0, t0, PMP_SHIFT
  csrw    pmpaddr0, t0

  la      t0, target_end
  srli    t0, t0, PMP_SHIFT
  csrw    pmpaddr1, t0

  li      t0, (PMP_TOR << 8) | PMP_RWX_TOR
  csrw    pmpcfg0, t0
  fence

  la      t0, probe_partial_top
  j       enter_s_mode

probe_partial_top:
  li      a0, 11
  la      t0, target
  ld      t1, 0(t0)
  ecall

# Phase 2: moving the effective top to target + 8 must allow the complete,
# naturally aligned doubleword.
setup_complete_top:
  csrw    pmpcfg0, zero

  la      t0, target
  addi    t0, t0, 8
  srli    t0, t0, PMP_SHIFT
  csrw    pmpaddr0, t0
  csrw    pmpaddr1, t0

  li      t0, (PMP_TOR << 8) | PMP_RWX_TOR
  csrw    pmpcfg0, t0
  fence

  la      t0, probe_complete_top
  j       enter_s_mode

probe_complete_top:
  li      a0, 21
  la      t0, target
  ld      t1, 0(t0)
  li      t2, SECRET
  bne     t1, t2, report_complete_top
  li      a0, 0
report_complete_top:
  ecall

# Phase 3: the same raw pmpaddr0 value is the top of an execute-only entry
# and the bottom of a read/write entry. Both uses must ignore bit 0, making
# target readable through entry 1 rather than denied by entry 0.
setup_shared_boundary:
  csrw    pmpcfg0, zero

  la      t0, target
  addi    t0, t0, 4
  srli    t0, t0, PMP_SHIFT
  csrw    pmpaddr0, t0

  la      t0, target_end
  srli    t0, t0, PMP_SHIFT
  csrw    pmpaddr1, t0

  li      t0, (PMP_RW_TOR << 8) | PMP_X_TOR
  csrw    pmpcfg0, t0
  fence

  la      t0, probe_shared_boundary
  j       enter_s_mode

probe_shared_boundary:
  li      a0, 31
  la      t0, target
  ld      t1, 0(t0)
  li      t2, SECRET
  bne     t1, t2, report_shared_boundary
  li      a0, 0
report_shared_boundary:
  ecall

enter_s_mode:
  li      t1, MSTATUS_MPP
  csrc    mstatus, t1
  li      t1, MSTATUS_MPP_S
  csrs    mstatus, t1
  csrw    mepc, t0
  mret

  .align 2
trap_handler:
  csrr    t0, mscratch
  li      t1, 1
  beq     t0, t1, handle_partial_top
  li      t1, 2
  beq     t0, t1, handle_complete_top
  li      t1, 3
  beq     t0, t1, handle_shared_boundary
  li      a0, 40
  j       finish

handle_partial_top:
  csrr    t0, mcause
  li      t1, CAUSE_LOAD_ACCESS_FAULT
  bne     t0, t1, finish

  li      t0, 2
  csrw    mscratch, t0
  j       setup_complete_top

handle_complete_top:
  csrr    t0, mcause
  li      t1, CAUSE_SUPERVISOR_ECALL
  bne     t0, t1, fail_complete_top
  bnez    a0, finish

  li      t0, 3
  csrw    mscratch, t0
  j       setup_shared_boundary

fail_complete_top:
  li      a0, 22
  j       finish

handle_shared_boundary:
  csrr    t0, mcause
  li      t1, CAUSE_SUPERVISOR_ECALL
  bne     t0, t1, fail_shared_boundary
  bnez    a0, finish
  li      a0, 0
  j       finish

fail_shared_boundary:
  li      a0, 32

finish:
  csrw    pmpcfg0, zero
  fence

  # Encode a0 using the RISC-V test convention and terminate through tohost.
  slli    a0, a0, 1
  ori     a0, a0, 1
  la      t0, tohost
  sd      a0, 0(t0)
1:
  j       1b

  .align 3
target:
  .dword  SECRET
target_end:
  .dword  0
