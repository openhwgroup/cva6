# Copyright 2023 Thales DIS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

#include "cvxif_macros.h"

#*****************************************************************************
# cvxif_s_mode.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
    ## set start address range t0 x7
    la x7, supervisor_code
    li x28, 0x10000
    add x7, x7, x28
    # Enable R,W,X,TOR IN PMPCFG CSR t0 x8
    li x8, 0x0F
    #set PMPADDR0 CSR with x7
    csrw 0x3B0, x7
    # set PMPCFG0 CSR with x8
    csrw 0x3A0, x8

    # Set the MPP field to supervisor mode (1)
    li x29, 0b01
    slli x29, x29, 11
    or x28, x28, x29

    # Write the modified MSTATUS value back to the CSR
    csrw 0x300, x28

    # Load address of supervisor code
    la x28, supervisor_code
    #set MEPC register to address of supervisor code
    csrw 0x341, x28

    csrr x31, 0x300
    mret
supervisor_code:

  CUS_S_ADD(01010,01010,01011);
  CUS_S_ADD(01010,11111,11010);
  CUS_ADD_MULTI(01010,01010,01011);
  CUS_ADD(11010,11001,11011);
  CUS_ADD(01010,01010,01011);
  CUS_S_ADD(10000,00010,00000);
  CUS_S_ADD(11111,11110,11111);
  CUS_S_ADD(00000,01010,01011);
  CUS_S_ADD(01010,01010,01011);
  CUS_ADD_MULTI(01010,00000,01011);
  CUS_S_ADD(11111,11111,01011);

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
