// Copyright (c) 2025 Thales DIS design services SAS
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Author: Maxime Colson - Thales
// Date: 20/03/2025
// Contributors: 
// Darshak Sheladiya, SYSGO GmbH
// Umberto Laghi, UNIBO

.section .text
.align 1 
.align 4 
.global branch_test
.type branch_test, @function


branch_test: 
    li x12,10
    loop:
        bne x13,x13, branch_test
        bne x13,x13, branch_test
        bne x13,x13, branch_test
        bne x13,x13, branch_test
        la x11, branch_test
        lw x10, 0(x11)
        bne x13,x13, branch_test
        bne x13,x13, branch_test
        bne x13,x13, branch_test
        bne x13,x13, branch_test
        bne x13,x13, branch_test
        bne x13,x13, branch_test
    addi x12,x12, -1
    bne x12, x0, loop


   jalr x0,0(ra)
