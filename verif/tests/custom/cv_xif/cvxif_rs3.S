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

    LOAD_RS(a0, 0x332211);
    LOAD_RS(a1, 0xDEADBEEF);
    LOAD_RS(a2, 0xDEADBEEF);

   CUS_ADD(01010,01010,01010,01011);
   CUS_ADD_RS3(01010,01010,01010,01011);
   CUS_ADD(01111,00111,00111,00011);
   CUS_ADD_RS3(01111,00111,00111,00011);
   CUS_ADD_RS3(10100,10010,10001,00100);
   CUS_ADD_RS3(11010,11001,10110,11011);
   CUS_ADD(01010,01010,01010,01011);
   CUS_ADD_RS3(11101,01100,00110,11111);
   CUS_ADD(11110,11000,11100,00001);
   CUS_ADD_RS3(01111,00111,00111,00011);

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
