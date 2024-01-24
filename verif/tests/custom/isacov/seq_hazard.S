# Copyright 2023 Thales DIS SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

#*****************************************************************************
# seq_hazard.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
# core of the test
  li         s1, 0x80000000 # Init reg value
  li         s2, 0x80000000
  li         a1, 0x1
  li         a2, 0x1
  csrr       s8, 0x340
  jal        a1, jump1

jump1:
  jalr       a1, a1, 8

jump2:
  jal        a1, jump3

jump3:
  sb         a1, 0(a1)
  jal        a1, jump4

jump4:       
  lb         a1, 0(a1)
  mul        a1, a1, s8
  csrrw      s8, 0x340, a1
  mul        a1, a2, s1
  lb         a1, 0(a1)
  div        a1, s1, a2
  lb         a1, 0(a1)
  jal        a1, jump5

jump5:
  csrrw      a1, 0x340, a1
  csrr       a1, 0x340
  jalr       a1, a1, 12
  jal        a1, jump6

jump6:
  sw         a1, 0(s2)
  lw         a1, 0(s2)
  jalr       t1, a1, 12
  jal        a1, jump7

jump7:
  mul        a1, a1, a2
  jalr       a1, a1, 8
  div        a1, a1, a2
  jalr       a1, a1, 8
  csrr       a1, 0x340
  lb         a1, 124(a1)

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
