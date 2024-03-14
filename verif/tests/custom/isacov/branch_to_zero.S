# Copyright 2023 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

#*****************************************************************************
# branch.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
# core of the test
  blt        zero, t3, main # BRANCH TO ZERO
  csrrs      s8, 0x340, a5
  li         a1, 0x1
  li         t0, 0x0
  beq        a1, t0, main
  bne        t0, t0, main
  blt        t0, t0, main
  bltu       a1, a1, main
  add        t5, a1 ,s6
  bge        zero, t5, main
  bgeu       zero, t5, main
  c.beqz     s0, main
  add        s1, zero ,zero
  c.bnez     s1, main
  add        s1, zero ,zero
branch:
  c.bnez     s1, branch
branch1:
  c.beqz     s0, branch1
branch2:
  bge        zero, t5, branch2
branch3:
  bltu       a1, a1, branch3
branch4:
  beq        zero, a1, branch4
branch5:
  bne        t5, t5, branch5
  addi       a0, a0, 22
  srl        a4, a5, a0
  csrrsi     t4, 0x340, 0
  sltiu      t4, s9, 236
  remu       t4, tp, a1
  c.andi     a5, -1
  lui        zero, 0
  beq        zero, zero, branch_to
branch_to:
  bne        zero, zero, main
  blt        zero, zero, main
  sub        a5, zero, a0
  bge        a5, zero, main

  #End of test
  j test_pass

test_pass:
    li ra, 0
    slli ra, ra, 1
    addi ra, ra, 1
    sw ra, tohost, t5
    self_loop: j self_loop

test_fail:
    li ra, 1
    slli ra, ra, 1
    addi ra, ra, 1
    sw ra, tohost, t5
    self_loop_2: j self_loop_2
