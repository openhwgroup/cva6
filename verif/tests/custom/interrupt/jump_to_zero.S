# Copyright 2024 Thales DIS SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

#*****************************************************************************
# jump_to_zero.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
# core of the test
  la t1, exception_handler
  csrw mtvec, t1  ## Load the address of the exception handler into MTVEC
  csrw 0x341, zero  ## Writing Zero to MEPC CSR
  csrw 0x342, zero  ## Writing Zero to MCAUSE CSR
  #End Handle exceptions

# enable interrupt in mie and mstatus
  li a1, 0x888
  csrw mie, a1
  csrr a2, mie
  li a1, 0x8
  csrw mstatus, a1
  csrr a2, mstatus

jump00:
  jal a1, jump00

jump01:
  c.j jump01

jump02:
  c.jal jump02

  #End of test
  j test_done

test_done:
    li ra, 0
    slli ra, ra, 1
    addi ra, ra, 1
    sw ra, tohost, t5
    self_loop: j self_loop

.align 8
exception_handler:
    # increment return address to skip instruction generating the exception
    # valid only if faulting instruction is not compressed (4-byte long)
    csrr  s11, mepc
    lbu  s5, 0(s11)
    li  s9, 0x3
    and  s5, s5, s9
    bne  s5, s9, exception_handler_incr_mepc2
    addi  s11, s11, 2
    exception_handler_incr_mepc2:
    addi  s11, s11, 2
    csrw  mepc, s11
    csrr t6, mepc
    mret
