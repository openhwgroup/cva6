# Copyright 2026 Keerthivasan
#
# Licensed under the Solderpad Hardware Licence, Version 2.0.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
# Regression test for CVA6 issue #3496.
#
# An interrupt must always write zero to mtinst.

  .section .text
  .align 2

  .equ MSTATUS_MIE,                0x00000008
  .equ MIP_SSIP,                   0x00000002
  .equ CAUSE_S_SOFT_INTERRUPT,     0x8000000000000001

  .globl main
  .globl handle_trap

main:
  # Keep the supervisor software interrupt in M-mode.
  csrw    medeleg, zero
  csrw    mideleg, zero

  # Start with interrupts and pending bits clear.
  csrw    mie, zero
  csrw    mip, zero

  # Keep a load ready when the pending interrupt becomes enabled.
  la      a1, irq_load_data

  # Enable and pend a supervisor software interrupt.
  li      t0, MIP_SSIP
  csrs    mie, t0
  csrs    mip, t0

  # Globally enable M-mode interrupts. Consecutive compressed loads below
  # ensure the interrupted instruction carries a non-zero transformed tinst
  # in the buggy implementation.
  li      t0, MSTATUS_MIE
  csrs    mstatus, t0

  .option push
  .option rvc
  c.ld    a2, 0(a1)
  c.ld    a2, 0(a1)
  c.ld    a2, 0(a1)
  c.ld    a2, 0(a1)
  c.ld    a2, 0(a1)
  c.ld    a2, 0(a1)
  c.ld    a2, 0(a1)
  c.ld    a2, 0(a1)
  .option pop

  # The interrupt must have been taken before reaching here.
  csrc    mstatus, t0
  csrw    mie, zero
  csrw    mip, zero

  li      a0, 3
  j       finish

handle_trap:
  # crt.S passes mcause in a0.
  li      t0, CAUSE_S_SOFT_INTERRUPT
  bne     a0, t0, fail_cause

  # Prevent another interrupt while finishing the test.
  csrw    mie, zero
  csrw    mip, zero

  # mtinst CSR = 0x34a.
  csrr    t0, 0x34a
  bnez    t0, fail_mtinst

pass:
  li      a0, 0
  j       finish

fail_cause:
  li      a0, 1
  j       finish

fail_mtinst:
  li      a0, 2

finish:
  jal     exit

  .section .data
  .align 3

irq_load_data:
  .dword  0x1122334455667788
