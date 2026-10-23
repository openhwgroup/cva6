# Copyright 2026 Keerthivasan
#
# Licensed under the Solderpad Hardware Licence, Version 2.0.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
# Regression test for CVA6 issue #3313.
#
# When MRET returns to M-mode, virtualization mode V must remain zero,
# regardless of the value previously stored in mstatus.MPV.
#
# V is internal architectural state and cannot be read directly.
# A subsequent trap to M-mode saves V into mstatus.MPV, allowing the
# post-MRET V state to be checked.

  .section .text
  .align 2

  .equ MSTATUS_MPP_MASK, 0x0000000000001800
  .equ MSTATUS_MPP_M,    0x0000000000001800
  .equ MSTATUS_MPV,      0x0000008000000000

  .equ CAUSE_ECALL_M,    11

  .globl main

main:
  # Send all exceptions used by this test to M-mode.
  la      t0, trap_handler
  csrw    mtvec, t0

  csrw    medeleg, zero
  csrw    mideleg, zero
  csrw    hedeleg, zero
  csrw    hideleg, zero

  # Configure MRET to return to M-mode.
  li      t0, MSTATUS_MPP_MASK
  csrc    mstatus, t0

  li      t0, MSTATUS_MPP_M
  csrs    mstatus, t0

  # Deliberately set MPV before MRET.
  #
  # The Hypervisor specification requires MRET to ignore MPV when
  # MPP=M and to keep virtualization mode V equal to zero.
  li      t0, MSTATUS_MPV
  csrc    mstatus, t0
  csrs    mstatus, t0

  # Confirm that MPV was writable so the test exercises the intended case.
  csrr    t0, mstatus
  li      t1, MSTATUS_MPV
  and     t2, t0, t1
  beqz    t2, fail_2

  la      t0, m_entry
  csrw    mepc, t0
  mret

m_entry:
  # Trap entry saves the current V state into mstatus.MPV.
  ecall

  # ECALL must trap.
  li      a0, 1
  j       finish

  .align 2
trap_handler:
  csrr    t0, mstatus

  # Main regression check.
  #
  # On the buggy RTL, MRET copies MPV=1 into V even though MPP=M.
  # Trap entry then saves that incorrect V=1 value back into MPV.
  li      t1, MSTATUS_MPV
  and     t2, t0, t1
  bnez    t2, fail_8

  # The trap must originate from M-mode.
  li      t1, MSTATUS_MPP_MASK
  and     t2, t0, t1
  li      t3, MSTATUS_MPP_M
  bne     t2, t3, fail_9

  # ECALL from M-mode must report exception cause 11.
  csrr    t0, mcause
  li      t1, CAUSE_ECALL_M
  bne     t0, t1, fail_3

pass:
  li      a0, 0
  j       finish

fail_2:
  # MPV was unavailable or not writable.
  li      a0, 2
  j       finish

fail_3:
  # Unexpected trap cause.
  li      a0, 3
  j       finish

fail_8:
  # Issue #3313 reproduced: V remained set after MRET to M-mode.
  li      a0, 8
  j       finish

fail_9:
  # Trap did not originate from M-mode.
  li      a0, 9

finish:
  jal     exit
