# Copyright 2026 Keerthivasan
#
# Licensed under the Solderpad Hardware Licence, Version 2.0.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
# Regression test for CVA6 issue #3294.
#
# MRET and SRET must clear mstatus.MPRV when returning to a
# privilege mode below M-mode, independently of RVH.

  .section .text
  .align 2

  .equ MSTATUS_SPP,      0x00000100
  .equ MSTATUS_MPP_MASK, 0x00001800
  .equ MSTATUS_MPP_S,    0x00000800
  .equ MSTATUS_MPP_M,    0x00001800
  .equ MSTATUS_MPRV,     0x00020000

  .equ CAUSE_ECALL_U,    8
  .equ CAUSE_ECALL_S,    9

  .globl main

main:
  # Route the ECALLs used by this test to M-mode.
  la      t0, trap_handler
  csrw    mtvec, t0
  csrw    medeleg, zero
  csrw    mideleg, zero

  # Run the lower-privilege portions of this regression in Bare mode.
  # The test exercises xRET privilege state, not virtual-memory setup.
  csrw    satp, zero
  sfence.vma

  # Permit S/U-mode execution of the test image.
  #
  # PMP entry 0 is configured as a TOR region from address zero to the
  # highest representable physical address, with read/write/execute
  # permissions enabled. The target implements PMP and otherwise resets
  # all entries with address matching disabled.
  li      t0, -1
  csrw    pmpaddr0, t0
  li      t0, 0x0f
  csrw    pmpcfg0, t0
  fence

  # ------------------------------------------------------------------
  # Phase 0: MRET from M-mode to M-mode.
  #
  # MPRV must be preserved when MRET returns to M-mode.
  # ------------------------------------------------------------------
  li      t0, MSTATUS_MPRV
  csrs    mstatus, t0

  li      t0, MSTATUS_MPP_MASK
  csrc    mstatus, t0

  li      t0, MSTATUS_MPP_M
  csrs    mstatus, t0

  # Verify MPRV is set before MRET.
  csrr    t0, mstatus
  li      t1, MSTATUS_MPRV
  and     t2, t0, t1
  beqz    t2, fail_mprv_write_mret

  la      t0, mret_m_entry
  csrw    mepc, t0
  mret

mret_m_entry:
  # MRET to M-mode must preserve MPRV.
  csrr    t0, mstatus
  li      t1, MSTATUS_MPRV
  and     t2, t0, t1
  beqz    t2, fail_mret_mprv_preserve

  # ------------------------------------------------------------------
  # Phase 1: MRET from M-mode to S-mode.
  # ------------------------------------------------------------------
  li      s0, 1

  # Configure MPRV=1 and MPP=S.
  li      t0, MSTATUS_MPRV
  csrc    mstatus, t0

  li      t0, MSTATUS_MPP_MASK
  csrc    mstatus, t0

  li      t0, MSTATUS_MPRV
  csrs    mstatus, t0

  li      t0, MSTATUS_MPP_S
  csrs    mstatus, t0

  # Ensure MPRV was actually writable.
  csrr    t0, mstatus
  li      t1, MSTATUS_MPRV
  and     t2, t0, t1
  beqz    t2, fail_mprv_write_mret

  # MRET must clear MPRV because the target privilege is S-mode.
  la      t0, mret_s_entry
  csrw    mepc, t0
  mret

mret_s_entry:
  # Return to M-mode so the trap handler can inspect mstatus.MPRV.
  ecall

  # ECALL must not return here.
  li      a0, 7
  j       finish

  # ------------------------------------------------------------------
  # Phase 2: SRET from M-mode to U-mode.
  # ------------------------------------------------------------------
sret_setup:
  li      s0, 2

  # Set MPRV=1 again.
  li      t0, MSTATUS_MPRV
  csrs    mstatus, t0

  # Configure SRET to return to U-mode by clearing SPP.
  li      t0, MSTATUS_SPP
  csrc    mstatus, t0

  # Ensure MPRV is set before SRET.
  csrr    t0, mstatus
  li      t1, MSTATUS_MPRV
  and     t2, t0, t1
  beqz    t2, fail_mprv_write_sret

  la      t0, sret_u_entry
  csrw    sepc, t0
  sret

sret_u_entry:
  # Return to M-mode so the trap handler can inspect MPRV.
  ecall

  # ECALL must not return here.
  li      a0, 8
  j       finish

  .align 2
trap_handler:
  li      t0, 1
  beq     s0, t0, check_mret

  li      t0, 2
  beq     s0, t0, check_sret

  li      a0, 9
  j       finish

check_mret:
  # ECALL must have originated from S-mode.
  csrr    t0, mcause
  li      t1, CAUSE_ECALL_S
  bne     t0, t1, fail_mret_cause

  # Main MRET regression check.
  csrr    t0, mstatus
  li      t1, MSTATUS_MPRV
  and     t2, t0, t1
  bnez    t2, fail_mret_mprv

  # Return from this M-mode trap to M-mode and start the SRET phase.
  la      t0, sret_setup
  csrw    mepc, t0

  li      t0, MSTATUS_MPP_MASK
  csrc    mstatus, t0

  li      t0, MSTATUS_MPP_M
  csrs    mstatus, t0

  mret

check_sret:
  # ECALL must have originated from U-mode.
  csrr    t0, mcause
  li      t1, CAUSE_ECALL_U
  bne     t0, t1, fail_sret_cause

  # Main SRET regression check.
  csrr    t0, mstatus
  li      t1, MSTATUS_MPRV
  and     t2, t0, t1
  bnez    t2, fail_sret_mprv

pass:
  li      a0, 0
  j       finish

fail_mprv_write_mret:
  li      a0, 1
  j       finish

fail_mret_cause:
  li      a0, 2
  j       finish

fail_mret_mprv:
  li      a0, 3
  j       finish

fail_mprv_write_sret:
  li      a0, 4
  j       finish

fail_sret_cause:
  li      a0, 5
  j       finish

fail_sret_mprv:
  li      a0, 6
  j       finish

fail_mret_mprv_preserve:
  li      a0, 10

finish:
  jal     exit
