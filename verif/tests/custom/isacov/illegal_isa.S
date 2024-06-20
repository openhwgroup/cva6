# Copyright 2024 Thales DIS SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

#*****************************************************************************
# illegal_test.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
    #Handle exceptions
    la x6, exception_handler
    csrw mtvec, x6  ## Load the address of the exception handler into MTVEC
    csrw 0x341, x0  ## Writing Zero to MEPC CSR
    csrw 0x342, x0  ## Writing Zero to MCAUSE CSR
    #End Handle exceptions
# core of the test

  #Cover Illegal funct7 corner case
  .4byte 0x5ad8f33
  #Cover illegal instruction similar to zext.h bitmanip instruction instr[24:20] != 0 in RV32 corner case
  .4byte 0x08824ab3
  #Cover illegal instruction similar to ctz bitmanip instruction with instr[24:20] != 1 in RV32 corner case
  .4byte 0x60971C13
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

.align 8
exception_handler:
    # increment return address to skip instruction generating the exception
    # valid only if faulting instruction is not compressed (4-byte long)
    csrr    x30, mepc  # mepc: 0x341
    addi    x30, x30, 4
    csrw    mepc, x30  # mepc: 0x341
    mret
