# Copyright 2026 Keerthivasan
#
# Licensed under the Solderpad Hardware Licence, Version 2.0.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
# Regression test for CVA6 issue #3457.
#
# Verify that medeleg[9] can retain the S-mode ECALL delegation
# bit and that an ECALL executed in S-mode is handled in S-mode.

  .section .text
  .align 2

  .equ MSTATUS_MPP_MASK, 0x00001800
  .equ MSTATUS_MPP_S,    0x00000800
  .equ MEDELEG_ECALL_S,  0x00000200
  .equ CAUSE_ECALL_S,    9

  .globl main

main:
  # Install separate M- and S-mode trap handlers.
  la      t0, m_trap_handler
  csrw    mtvec, t0

  la      t0, s_trap_handler
  csrw    stvec, t0

  # This regression does not exercise virtual memory.
  csrw    satp, zero
  sfence.vma

  # Permit S-mode execution and data accesses over the test image.
  li      t0, -1
  csrw    pmpaddr0, t0

  li      t0, 0x0f
  csrw    pmpcfg0, t0
  fence

  # Request delegation of ECALL-from-S-mode, cause 9.
  li      t0, MEDELEG_ECALL_S
  csrw    medeleg, t0

  # Preserve readback so the trap handlers can distinguish
  # CSR-write failure from trap-routing failure.
  csrr    s0, medeleg

  # Enter S-mode.
  li      t0, MSTATUS_MPP_MASK
  csrc    mstatus, t0

  li      t0, MSTATUS_MPP_S
  csrs    mstatus, t0

  la      t0, s_ecall_site
  csrw    mepc, t0
  mret

s_ecall_site:
  ecall

  # A correctly delegated ECALL must not resume here.
  li      a0, 2
  j       finish

  .align 2
s_trap_handler:
  # ECALL from S-mode must report cause 9.
  csrr    t0, scause
  li      t1, CAUSE_ECALL_S
  bne     t0, t1, fail_scause

  # sepc must point at the ECALL itself.
  csrr    t0, sepc
  la      t1, s_ecall_site
  bne     t0, t1, fail_sepc

  # Confirm that medeleg[9] really read back as set.
  li      t0, MEDELEG_ECALL_S
  and     t1, s0, t0
  beqz    t1, fail_s_readback

  li      a0, 0
  j       finish

  .align 2
m_trap_handler:
  # If we arrived here, ECALL delegation failed.
  # Distinguish a missing CSR bit from a routing failure.
  li      t0, MEDELEG_ECALL_S
  and     t1, s0, t0
  beqz    t1, fail_m_readback

  li      a0, 92
  j       finish

fail_s_readback:
  li      a0, 83
  j       finish

fail_m_readback:
  li      a0, 91
  j       finish

fail_scause:
  li      a0, 5
  j       finish

fail_sepc:
  li      a0, 6

finish:
  jal     exit
