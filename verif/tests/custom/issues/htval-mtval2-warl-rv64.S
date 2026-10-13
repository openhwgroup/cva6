# Copyright 2026 Keerthivasan
#
# Licensed under the Solderpad Hardware Licence, Version 2.0.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
# Regression test for CVA6 issue #3537.
#
# On RV64 Sv39x4, guest physical addresses are 41 bits. htval and
# mtval2 store the guest physical address shifted right by two, so
# only bits [38:0] of these CSRs are meaningful.

  .section .text
  .align 2

  .equ CSR_MTVAL2, 0x34b
  .equ CSR_HTVAL,  0x643

  .equ SHIFTED_GPA_MASK_SV39X4, 0x0000007fffffffff

  .globl main

main:
  li      t0, -1
  li      t2, SHIFTED_GPA_MASK_SV39X4

  # htval must legalize values outside the implemented shifted-GPA width.
  csrw    CSR_HTVAL, t0
  csrr    t1, CSR_HTVAL
  bne     t1, t2, fail_htval

  # mtval2 must follow the same WARL behavior.
  csrw    CSR_MTVAL2, t0
  csrr    t1, CSR_MTVAL2
  bne     t1, t2, fail_mtval2

  # Both WARL registers must be capable of holding zero.
  csrw    CSR_HTVAL, zero
  csrr    t1, CSR_HTVAL
  bnez    t1, fail_htval_zero

  csrw    CSR_MTVAL2, zero
  csrr    t1, CSR_MTVAL2
  bnez    t1, fail_mtval2_zero

pass:
  li      a0, 0
  j       finish

fail_htval:
  li      a0, 1
  j       finish

fail_mtval2:
  li      a0, 2
  j       finish

fail_htval_zero:
  li      a0, 3
  j       finish

fail_mtval2_zero:
  li      a0, 4

finish:
  jal     exit
