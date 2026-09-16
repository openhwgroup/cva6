# Copyright 2026 Keerthivasan
#
# Licensed under the Solderpad Hardware Licence, Version 2.0.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
# Regression test for CVA6 issue #3458.
#
# mtvec is WARL. If an mtvec value contains address bits that the
# implementation cannot use for instruction fetch, the implementation may
# legalize the value on write. If the value is instead retained on readback,
# trap dispatch must consume the same architectural base.
#
# The current bug retains a high-tagged value in mtvec, while the instruction
# fetch path ultimately uses the low physical-address alias.

  .section .text
  .align 2

  .equ HIGH_TAG, 0x1000000000000000

  .globl main

main:
  # Construct an mtvec value whose low portion names a real executable
  # trap handler while bit 60 is outside the implemented physical-address
  # width of cv64a6_imafdc_sv39.
  la      t0, low_trap_entry
  li      t1, HIGH_TAG
  or      s0, t0, t1

  # Write and immediately read back mtvec.
  csrw    mtvec, s0
  csrr    s1, mtvec

  # Legalization is a valid WARL implementation choice.
  # If the unsupported tag was removed, the CSR and fetch behavior are
  # coherent and this test passes.
  bne     s1, s0, pass_mtvec_legalized

  # If the tagged value was retained, trap dispatch must not silently
  # consume the low alias.
ecall_site:
  ecall

  # ECALL must trap and must never retire here.
  li      a0, 41
  j       finish

  .align 2
low_trap_entry:
  # Reaching this handler while mtvec readback retained HIGH_TAG reproduces
  # issue #3458: software sees the tagged base but hardware dispatched to
  # its low physical alias.
  li      a0, 42
  j       finish

pass_mtvec_legalized:
  li      a0, 0

finish:
  jal     exit
