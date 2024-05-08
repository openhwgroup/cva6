# Copyright 2024 Thales DIS SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

#*****************************************************************************
# jump_test.S
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

  #trying to cover value zero of rs1 with a negative value of imm
  jalr t6, zero, -1
  #trying to cover value zero of rs1 with a zero value of imm
  jalr t6, zero, 0
  #trying to cover value zero of rs1 with a positive value of imm
  jalr t6, zero, 1
  addi t6, t6, 6
  li s0, 0x0
  #trying to cover value zero of rs1
  c.jalr s0
  addi t6, t6, 4
  #trying to cover value zero of rs1
  c.jr s0

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
    csrr    t0, mepc
    csrr    t0, mcause
    csrw    mepc, t6
    mret
