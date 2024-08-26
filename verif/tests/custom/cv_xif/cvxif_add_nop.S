# See LICENSE for license details.

#*****************************************************************************
# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https:#solderpad.org/licenses/
#
#----------------------------------------------------------------------------------

#include "cvxif_macros.h"

  #-------------------------------------------------------------
  # Custom tests
  #-------------------------------------------------------------

  .globl main
main:

# core of the test

start0:
    LOAD_RS(a0, 0x332211);
    LOAD_RS(a1, 0xDEADBEEF);
    LOAD_RS(a2, 0xDEADBEEF);
    CUS_NOP();
    CUS_ADD(01010, 01010, 01011);
    CUS_ADD(01011, 01010, 01011);
    CUS_ADD(01010, 01011, 01011);
    lw a0, num1;
    CUS_ADD_RS1(01100,01010,01011);
    lw a1, num2;
    CUS_ADD(01010,01011,00000);

# Take branch to check for instruction kill
    li a0, 0xCAFE;
    li a1, 0xCAFE;
    xor a2, a0, a1;
    beqz a2, branch2;

branch1:
    CUS_ADD(00000, 00000, 01011);
    CUS_NOP();
    CUS_NOP();

branch2:
    CUS_ADD(01010, 01010, 01011);
    lw a0, num1;
    CUS_ADD_RS1(01100,01010,01011);
    lw a1, num2;
    CUS_ADD(01010,01011,00000);

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

.data
    num1:   .word 5      // First number
    num2:   .word 7      // Second number
    result: .word 12      // Result