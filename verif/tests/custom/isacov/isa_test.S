# Copyright 2024 Thales DIS SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

#*****************************************************************************
# isa_test.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
# core of the test

  slli zero, zero, 0
  slli ra, ra, 0
  slli sp, sp, 0
  slli gp, gp, 0
  slli tp, tp, 0
  slli t0, t0, 0
  slli t1, t1, 0
  slli t2, t2, 0
  slli s0, s0, 0
  slli s1, s1, 0
  slli a0, a0, 0
  slli a1, a1, 0
  slli a2, a2, 0
  slli a3, a3, 0
  slli a4, a4, 0
  slli a5, a5, 0
  slli a6, a6, 0
  slli a7, a7, 0
  slli s2, s2, 0
  slli s3, s3, 0
  slli s4, s4, 0
  slli s5, s5, 0
  slli s6, s6, 0
  slli s7, s7, 0
  slli s8, s8, 0
  slli s9, s9, 0
  slli s10, s10, 0
  slli s11, s11, 0
  slli t3, t3, 0
  slli t4, t4, 0
  slli t5, t5, 0
  slli t6, t6, 0

  slti zero, zero, 0
  slti ra, ra, 0
  slti sp, sp, 0
  slti gp, gp, 0
  slti tp, tp, 0
  slti t0, t0, 0
  slti t1, t1, 0
  slti t2, t2, 0
  slti s0, s0, 0
  slti s1, s1, 0
  slti a0, a0, 0
  slti a1, a1, 0
  slti a2, a2, 0
  slti a3, a3, 0
  slti a4, a4, 0
  slti a5, a5, 0
  slti a6, a6, 0
  slti a7, a7, 0
  slti s2, s2, 0
  slti s3, s3, 0
  slti s4, s4, 0
  slti s5, s5, 0
  slti s6, s6, 0
  slti s7, s7, 0
  slti s8, s8, 0
  slti s9, s9, 0
  slti s10, s10, 0
  slti s11, s11, 0
  slti t3, t3, 0
  slti t4, t4, 0
  slti t5, t5, 0
  slti t6, t6, 0

  sltiu zero, zero, 0
  sltiu ra, ra, 0
  sltiu sp, sp, 0
  sltiu gp, gp, 0
  sltiu tp, tp, 0
  sltiu t0, t0, 0
  sltiu t1, t1, 0
  sltiu t2, t2, 0
  sltiu s0, s0, 0
  sltiu s1, s1, 0
  sltiu a0, a0, 0
  sltiu a1, a1, 0
  sltiu a2, a2, 0
  sltiu a3, a3, 0
  sltiu a4, a4, 0
  sltiu a5, a5, 0
  sltiu a6, a6, 0
  sltiu a7, a7, 0
  sltiu s2, s2, 0
  sltiu s3, s3, 0
  sltiu s4, s4, 0
  sltiu s5, s5, 0
  sltiu s6, s6, 0
  sltiu s7, s7, 0
  sltiu s8, s8, 0
  sltiu s9, s9, 0
  sltiu s10, s10, 0
  sltiu s11, s11, 0
  sltiu t3, t3, 0
  sltiu t4, t4, 0
  sltiu t5, t5, 0
  sltiu t6, t6, 0

  sltu zero, zero, zero

  srai zero, zero, 0
  srai ra, ra, 0
  srai sp, sp, 0
  srai gp, gp, 0
  srai tp, tp, 0
  srai t0, t0, 0
  srai t1, t1, 0
  srai t2, t2, 0
  srai s0, s0, 0
  srai s1, s1, 0
  srai a0, a0, 0
  srai a1, a1, 0
  srai a2, a2, 0
  srai a3, a3, 0
  srai a4, a4, 0
  srai a5, a5, 0
  srai a6, a6, 0
  srai a7, a7, 0
  srai s2, s2, 0
  srai s3, s3, 0
  srai s4, s4, 0
  srai s5, s5, 0
  srai s6, s6, 0
  srai s7, s7, 0
  srai s8, s8, 0
  srai s9, s9, 0
  srai s10, s10, 0
  srai s11, s11, 0
  srai t3, t3, 0
  srai t4, t4, 0
  srai t5, t5, 0
  srai t6, t6, 0

  srli zero, zero, 0
  srli ra, ra, 0
  srli sp, sp, 0
  srli gp, gp, 0
  srli tp, tp, 0
  srli t0, t0, 0
  srli t1, t1, 0
  srli t2, t2, 0
  srli s0, s0, 0
  srli s1, s1, 0
  srli a0, a0, 0
  srli a1, a1, 0
  srli a2, a2, 0
  srli a3, a3, 0
  srli a4, a4, 0
  srli a5, a5, 0
  srli a6, a6, 0
  srli a7, a7, 0
  srli s2, s2, 0
  srli s3, s3, 0
  srli s4, s4, 0
  srli s5, s5, 0
  srli s6, s6, 0
  srli s7, s7, 0
  srli s8, s8, 0
  srli s9, s9, 0
  srli s10, s10, 0
  srli s11, s11, 0
  srli t3, t3, 0
  srli t4, t4, 0
  srli t5, t5, 0
  srli t6, t6, 0

  csrrw zero, mscratch, zero
  csrrw ra, mscratch, ra
  csrrw sp, mscratch, sp
  csrrw gp, mscratch, gp
  csrrw tp, mscratch, tp
  csrrw t0, mscratch, t0
  csrrw t1, mscratch, t1
  csrrw t2, mscratch, t2
  csrrw s0, mscratch, s0
  csrrw s1, mscratch, s1
  csrrw a0, mscratch, a0
  csrrw a1, mscratch, a1
  csrrw a2, mscratch, a2
  csrrw a3, mscratch, a3
  csrrw a4, mscratch, a4
  csrrw a5, mscratch, a5
  csrrw a6, mscratch, a6
  csrrw a7, mscratch, a7
  csrrw s2, mscratch, s2
  csrrw s3, mscratch, s3
  csrrw s4, mscratch, s4
  csrrw s5, mscratch, s5
  csrrw s6, mscratch, s6
  csrrw s7, mscratch, s7
  csrrw s8, mscratch, s8
  csrrw s9, mscratch, s9
  csrrw s10, mscratch, s10
  csrrw s11, mscratch, s11
  csrrw t3, mscratch, t3
  csrrw t4, mscratch, t4
  csrrw t5, mscratch, t5
  csrrw t6, mscratch, t6

  csrrs zero, mscratch, zero
  csrrs ra, mscratch, ra
  csrrs sp, mscratch, sp
  csrrs gp, mscratch, gp
  csrrs tp, mscratch, tp
  csrrs t0, mscratch, t0
  csrrs t1, mscratch, t1
  csrrs t2, mscratch, t2
  csrrs s0, mscratch, s0
  csrrs s1, mscratch, s1
  csrrs a0, mscratch, a0
  csrrs a1, mscratch, a1
  csrrs a2, mscratch, a2
  csrrs a3, mscratch, a3
  csrrs a4, mscratch, a4
  csrrs a5, mscratch, a5
  csrrs a6, mscratch, a6
  csrrs a7, mscratch, a7
  csrrs s2, mscratch, s2
  csrrs s3, mscratch, s3
  csrrs s4, mscratch, s4
  csrrs s5, mscratch, s5
  csrrs s6, mscratch, s6
  csrrs s7, mscratch, s7
  csrrs s8, mscratch, s8
  csrrs s9, mscratch, s9
  csrrs s10, mscratch, s10
  csrrs s11, mscratch, s11
  csrrs t3, mscratch, t3
  csrrs t4, mscratch, t4
  csrrs t5, mscratch, t5
  csrrs t6, mscratch, t6

  csrrc zero, mscratch, zero
  csrrc ra, mscratch, ra
  csrrc sp, mscratch, sp
  csrrc gp, mscratch, gp
  csrrc tp, mscratch, tp
  csrrc t0, mscratch, t0
  csrrc t1, mscratch, t1
  csrrc t2, mscratch, t2
  csrrc s0, mscratch, s0
  csrrc s1, mscratch, s1
  csrrc a0, mscratch, a0
  csrrc a1, mscratch, a1
  csrrc a2, mscratch, a2
  csrrc a3, mscratch, a3
  csrrc a4, mscratch, a4
  csrrc a5, mscratch, a5
  csrrc a6, mscratch, a6
  csrrc a7, mscratch, a7
  csrrc s2, mscratch, s2
  csrrc s3, mscratch, s3
  csrrc s4, mscratch, s4
  csrrc s5, mscratch, s5
  csrrc s6, mscratch, s6
  csrrc s7, mscratch, s7
  csrrc s8, mscratch, s8
  csrrc s9, mscratch, s9
  csrrc s10, mscratch, s10
  csrrc s11, mscratch, s11
  csrrc t3, mscratch, t3
  csrrc t4, mscratch, t4
  csrrc t5, mscratch, t5
  csrrc t6, mscratch, t6

  csrrwi zero, mscratch, 0
  csrrsi zero, mscratch, 0
  csrrci zero, mscratch, 0

  add zero, zero, zero
  add ra, ra, zero
  add sp, sp, zero
  add gp, gp, zero
  add tp, tp, zero
  add t0, t0, zero
  add t1, t1, zero
  add t2, t2, zero
  add s0, s0, zero
  add s1, s1, zero
  add a0, a0, zero
  add a1, a1, zero
  add a2, a2, zero
  add a3, a3, zero
  add a4, a4, zero
  add a5, a5, zero
  add a6, a6, zero
  add a7, a7, zero
  add s2, s2, zero
  add s3, s3, zero
  add s4, s4, zero
  add s5, s5, zero
  add s6, s6, zero
  add s7, s7, zero
  add s8, s8, zero
  add s9, s9, zero
  add s10, s10, zero
  add s11, s11, zero
  add t3, t3, zero
  add t4, t4, zero
  add t5, t5, zero
  add t6, t6, zero

  andi t6, zero, 0
  xori t6, zero, 0

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
