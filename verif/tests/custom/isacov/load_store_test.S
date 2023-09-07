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
  mulhu      s11, t3, s3
  srl        a3, s2, gp
  c.mv       sp, s5
  addi       a1, a1, -856
  or         s7, t0, a5
  remu       a3, s5, t5
  c.nop
  li         s3, 0x0 #start riscv_int_numeric_corner_stream_0
  li         s1, 0xffffffff
  li         a5, 0x80000000
  li         sp, 0x80000000
  li         s10, 0x80000000
  li         t2, 0xffffffff
  li         t0, 0x0
  li         s6, 0x80000000
  li         tp, 0xffffffff
  li         ra, 0x0
  addi       s1, zero,0xffffff00
  c.lwsp     sp, 0(sp)
  lb         t0, 0(s1)
  lh         t0, 0(s1)
  lw         t0, 0(s1)
  lbu        t0, 0(s1)
  lhu        t0, 0(s1)
  sb         t0, 0(s1)
  sh         t0, 0(s1)
  sw         t0, 0(s1)
  sb         t0, -16(zero)
  sh         t0, -16(zero)
  sw         t0, -16(zero)
  addi       a0, zero,0xffffff00
  c.sw       a2, 124(a0)
  c.lw       a0,  124(s1)
  c.sw       a0,  124(s1)
  c.sw       a0, 124(a5)
  mul        a5, ra, s1
  divu       s6, ra, s6
  auipc      s10, 1013927
  sub        ra, ra, s10
  div        t0, t2, ra
# (example of) final self-check test
  li a0, 0xCAFE;
  li a1, 0xCAFE;
  xor a2, a0, a1;
  beqz a2, pass;

fail:
  # Failure post-processing (messages, ecall setup etc.)
  li a0, 0x0;
  jal exit;

pass:
  # Success post-processing (messages, ecall setup etc.)
  li a0, 0x0;
  jal exit;
