# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

#include "csrrst_test.S"
#include "csrrw_fields_test.S"
#include "csrrw_test.S"
#include "csrrwi_test.S"
#include "csrcs_test.S"
#include "csrcsi_test.S"

.globl main
main:
    #Start CSR tests: all tests
    call csrrst
    call csrrw_fields
    call csrrw
    call csrrwi
    call csrcs
    call csrcsi

    #End of csr test
    j csr_pass

csr_pass:
    li x1, 0
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop: j self_loop

csr_fail:
    li x1, 1
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop_2: j self_loop_2

