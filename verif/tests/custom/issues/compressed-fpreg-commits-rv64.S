# Copyright 2022 Thales DIS France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Zbigniew CHAMSKI (zbigniew.chamski@thalesgroup.fr)

#*****************************************************************************
# compressed-fpreg-commits.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
  la s1, tohost;
  c.fld  fs0, 0(s1);
  c.fldsp fs1, 0(sp);
  xor a2, a0, a0;  # trivial PASS...
  beqz a2, pass;

fail:
  # Failure post-processing; set retcode to 1.
  li a0, 0x1;
  jal exit;

pass:
  # Success post-processing: set retcode to 0.
  li a0, 0x0;
  jal exit;

