# Copyright 2026 Keerthivasan
#
# Licensed under the Solderpad Hardware Licence, Version 2.0.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
# Regression test for CVA6 issue #3496.
#
# A virtual-instruction trap must not write a transformed standard
# instruction to mtinst.

  .section .text
  .align 2

  .equ MSTATUS_MPP_MASK,          0x00001800
  .equ MSTATUS_MPP_S,             0x00000800
  .equ MSTATUS_MPV,               0x0000008000000000
  .equ CAUSE_VIRTUAL_INSTRUCTION, 22

  .globl main
  .globl handle_trap

main:
  # Keep the test in bare translation modes.
  csrw    satp, zero
  csrw    vsatp, zero
  csrw    hgatp, zero
  sfence.vma

  # Do not delegate the virtual-instruction exception to HS-mode.
  csrw    medeleg, zero
  csrw    mideleg, zero

  # Allow lower privilege modes to execute the test image.
  li      t0, -1
  csrw    pmpaddr0, t0
  li      t0, 0x0f
  csrw    pmpcfg0, t0
  fence

  # Configure MRET to enter VS-mode:
  # MPP=S and MPV=1.
  li      t0, MSTATUS_MPP_MASK
  csrc    mstatus, t0

  li      t0, MSTATUS_MPV
  csrc    mstatus, t0

  li      t0, MSTATUS_MPP_S
  csrs    mstatus, t0

  li      t0, MSTATUS_MPV
  csrs    mstatus, t0

  la      t0, vs_entry
  csrw    mepc, t0
  mret

vs_entry:
  # HLV.B a0, (x0)
  #
  # HLV is not executable while V=1. This therefore raises a
  # virtual-instruction exception. The buggy RTL writes the transformed
  # HLV.B encoding into mtinst instead of zero.
  .word   0x60004573

  # The instruction must not complete normally.
  li      a0, 3
  j       finish

handle_trap:
  # crt.S passes mcause in a0.
  li      t0, CAUSE_VIRTUAL_INSTRUCTION
  bne     a0, t0, fail_cause

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
