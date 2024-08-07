# Copyright 2023 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

#*****************************************************************************
# load_reg_hazard.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
  li         ra, 0x80000000
  li         sp, 0x80000000
  li         gp, 0x80000000
  li         tp, 0x80000000
  li         t0, 0x80000000
  li         t1, 0x80000000
  li         t2, 0x80000000
  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000
  li         a6, 0x80000000
  li         a7, 0x80000000
  li         s2, 0x80000000
  li         s3, 0x80000000
  li         s4, 0x80000000
  li         s5, 0x80000000
  li         s6, 0x80000000
  li         s7, 0x80000000
  li         s8, 0x80000000
  li         s9, 0x80000000
  li         s10, 0x80000000
  li         s11, 0x80000000
  li         t3, 0x80000000
  li         t4, 0x80000000
  li         t5, 0x80000000
  li         t6, 0x80000000

  lw         sp, 1024(sp)
  lw         ra, 52(ra)
  lw         gp, 52(gp)
  lw         tp, 52(tp)
  lw         t0, 52(t0)
  lw         t1, 52(t1)
  lw         t2, 52(t2)
  lw         s0, 1024(s0)
  lw         s1, 1024(s1)
  lw         a0, 1024(a0)
  lw         a1, 1024(a1)
  lw         a2, 1024(a2)
  lw         a3, 1024(a3)
  lw         a4, 1024(a4)
  lw         a5, 1024(a5)
  lw         a6, 1024(a6)
  lw         a7, 1024(a7)
  lw         s2, 52(s2)
  lw         s3, 52(s3)
  lw         s4, 52(s4)
  lw         s5, 72(s5)
  lw         s6, 76(s6)
  lw         s7, 80(s7)
  lw         s8, 84(s8)
  lw         s9, 88(s9)
  lw         s10, 92(s10)
  lw         s11, 96(s11)
  lw         t3, 12(t3)
  lw         t4, 16(t4)
  lw         t5, 12(t5)
  lw         t6, 16(t6)
  li         ra, 0x80000000
  li         sp, 0x80000000
  li         gp, 0x80000000
  li         tp, 0x80000000
  li         t0, 0x80000000
  li         t1, 0x80000000
  li         t2, 0x80000000
  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000
  li         a6, 0x80000000
  li         a7, 0x80000000
  li         s2, 0x80000000
  li         s3, 0x80000000
  li         s4, 0x80000000
  li         s5, 0x80000000
  li         s6, 0x80000000
  li         s7, 0x80000000
  li         s8, 0x80000000
  li         s9, 0x80000000
  li         s10, 0x80000000
  li         s11, 0x80000000
  li         t3, 0x80000000
  li         t4, 0x80000000
  li         t5, 0x80000000
  li         t6, 0x80000000

  lh         sp, 1024(sp)
  lh         ra, 52(ra)
  lh         gp, 52(gp)
  lh         tp, 52(tp)
  lh         t0, 52(t0)
  lh         t1, 52(t1)
  lh         t2, 52(t2)
  lh         s0, 1024(s0)
  lh         s1, 1024(s1)
  lh         a0, 1024(a0)
  lh         a1, 1024(a1)
  lh         a2, 1024(a2)
  lh         a3, 1024(a3)
  lh         a4, 1024(a4)
  lh         a5, 1024(a5)
  lh         a6, 1024(a6)
  lh         a7, 1024(a7)
  lh         s2, 52(s2)
  lh         s3, 52(s3)
  lh         s4, 52(s4)
  lh         s5, 72(s5)
  lh         s6, 76(s6)
  lh         s7, 80(s7)
  lh         s8, 84(s8)
  lh         s9, 88(s9)
  lh         s10, 92(s10)
  lh         s11, 96(s11)
  lh         t3, 12(t3)
  lh         t4, 16(t4)
  lh         t5, 12(t5)
  lh         t6, 16(t6)
  li         ra, 0x80000000
  li         sp, 0x80000000
  li         gp, 0x80000000
  li         tp, 0x80000000
  li         t0, 0x80000000
  li         t1, 0x80000000
  li         t2, 0x80000000
  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000
  li         a6, 0x80000000
  li         a7, 0x80000000
  li         s2, 0x80000000
  li         s3, 0x80000000
  li         s4, 0x80000000
  li         s5, 0x80000000
  li         s6, 0x80000000
  li         s7, 0x80000000
  li         s8, 0x80000000
  li         s9, 0x80000000
  li         s10, 0x80000000
  li         s11, 0x80000000
  li         t3, 0x80000000
  li         t4, 0x80000000
  li         t5, 0x80000000
  li         t6, 0x80000000

  lb         sp, 1024(sp)
  lb         ra, 52(ra)
  lb         gp, 52(gp)
  lb         tp, 52(tp)
  lb         t0, 52(t0)
  lb         t1, 52(t1)
  lb         t2, 52(t2)
  lb         s0, 1024(s0)
  lb         s1, 1024(s1)
  lb         a0, 1024(a0)
  lb         a1, 1024(a1)
  lb         a2, 1024(a2)
  lb         a3, 1024(a3)
  lb         a4, 1024(a4)
  lb         a5, 1024(a5)
  lb         a6, 1024(a6)
  lb         a7, 1024(a7)
  lb         s2, 52(s2)
  lb         s3, 52(s3)
  lb         s4, 52(s4)
  lb         s5, 72(s5)
  lb         s6, 76(s6)
  lb         s7, 80(s7)
  lb         s8, 84(s8)
  lb         s9, 88(s9)
  lb         s10, 92(s10)
  lb         s11, 96(s11)
  lb         t3, 12(t3)
  lb         t4, 16(t4)
  lb         t5, 12(t5)
  lb         t6, 16(t6)
  li         ra, 0x80000000
  li         sp, 0x80000000
  li         gp, 0x80000000
  li         tp, 0x80000000
  li         t0, 0x80000000
  li         t1, 0x80000000
  li         t2, 0x80000000
  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000
  li         a6, 0x80000000
  li         a7, 0x80000000
  li         s2, 0x80000000
  li         s3, 0x80000000
  li         s4, 0x80000000
  li         s5, 0x80000000
  li         s6, 0x80000000
  li         s7, 0x80000000
  li         s8, 0x80000000
  li         s9, 0x80000000
  li         s10, 0x80000000
  li         s11, 0x80000000
  li         t3, 0x80000000
  li         t4, 0x80000000
  li         t5, 0x80000000
  li         t6, 0x80000000

  lbu         sp, 1024(sp)
  lbu         ra, 52(ra)
  lbu         gp, 52(gp)
  lbu         tp, 52(tp)
  lbu         t0, 52(t0)
  lbu         t1, 52(t1)
  lbu         t2, 52(t2)
  lbu         s0, 1024(s0)
  lbu         s1, 1024(s1)
  lbu         a0, 1024(a0)
  lbu         a1, 1024(a1)
  lbu         a2, 1024(a2)
  lbu         a3, 1024(a3)
  lbu         a4, 1024(a4)
  lbu         a5, 1024(a5)
  lbu         a6, 1024(a6)
  lbu         a7, 1024(a7)
  lbu         s2, 52(s2)
  lbu         s3, 52(s3)
  lbu         s4, 52(s4)
  lbu         s5, 72(s5)
  lbu         s6, 76(s6)
  lbu         s7, 80(s7)
  lbu         s8, 84(s8)
  lbu         s9, 88(s9)
  lbu         s10, 92(s10)
  lbu         s11, 96(s11)
  lbu         t3, 12(t3)
  lbu         t4, 16(t4)
  lbu         t5, 12(t5)
  lbu         t6, 16(t6)
  li         ra, 0x80000000
  li         sp, 0x80000000
  li         gp, 0x80000000
  li         tp, 0x80000000
  li         t0, 0x80000000
  li         t1, 0x80000000
  li         t2, 0x80000000
  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000
  li         a6, 0x80000000
  li         a7, 0x80000000
  li         s2, 0x80000000
  li         s3, 0x80000000
  li         s4, 0x80000000
  li         s5, 0x80000000
  li         s6, 0x80000000
  li         s7, 0x80000000
  li         s8, 0x80000000
  li         s9, 0x80000000
  li         s10, 0x80000000
  li         s11, 0x80000000
  li         t3, 0x80000000
  li         t4, 0x80000000
  li         t5, 0x80000000
  li         t6, 0x80000000

  lhu         sp, 1024(sp)
  lhu         ra, 52(ra)
  lhu         gp, 52(gp)
  lhu         tp, 52(tp)
  lhu         t0, 52(t0)
  lhu         t1, 52(t1)
  lhu         t2, 52(t2)
  lhu         s0, 1024(s0)
  lhu         s1, 1024(s1)
  lhu         a0, 1024(a0)
  lhu         a1, 1024(a1)
  lhu         a2, 1024(a2)
  lhu         a3, 1024(a3)
  lhu         a4, 1024(a4)
  lhu         a5, 1024(a5)
  lhu         a6, 1024(a6)
  lhu         a7, 1024(a7)
  lhu         s2, 52(s2)
  lhu         s3, 52(s3)
  lhu         s4, 52(s4)
  lhu         s5, 72(s5)
  lhu         s6, 76(s6)
  lhu         s7, 80(s7)
  lhu         s8, 84(s8)
  lhu         s9, 88(s9)
  lhu         s10, 92(s10)
  lhu         s11, 96(s11)
  lhu         t3, 12(t3)
  lhu         t4, 16(t4)
  lhu         t5, 12(t5)
  lhu         t6, 16(t6)

  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000

  c.lbu         s0, 2(s0)
  c.lbu         s1, 2(s1)
  c.lbu         a0, 2(a0)
  c.lbu         a1, 2(a1)
  c.lbu         a2, 2(a2)
  c.lbu         a3, 2(a3)
  c.lbu         a4, 2(a4)
  c.lbu         a5, 2(a5)

  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000

  c.lh         s0, 0(s0)
  c.lh         s1, 0(s1)
  c.lh         a0, 0(a0)
  c.lh         a1, 0(a1)
  c.lh         a2, 0(a2)
  c.lh         a3, 0(a3)
  c.lh         a4, 0(a4)
  c.lh         a5, 0(a5)

  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000

  c.lhu         s0, 0(s0)
  c.lhu         s1, 0(s1)
  c.lhu         a0, 0(a0)
  c.lhu         a1, 0(a1)
  c.lhu         a2, 0(a2)
  c.lhu         a3, 0(a3)
  c.lhu         a4, 0(a4)
  c.lhu         a5, 0(a5)

  li         s0, 0x80000000
  li         s1, 0x80000000
  li         a0, 0x80000000
  li         a1, 0x80000000
  li         a2, 0x80000000
  li         a3, 0x80000000
  li         a4, 0x80000000
  li         a5, 0x80000000

  c.lw          s0, 0(s0)
  c.lw          s1, 0(s1)
  c.lw          a0, 0(a0)
  c.lw          a1, 0(a1)
  c.lw          a2, 0(a2)
  c.lw          a3, 0(a3)
  c.lw          a4, 0(a4)
  c.lw          a5, 0(a5)

  li         sp, 0x80000000
  c.lwsp     sp, 0(sp)

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
