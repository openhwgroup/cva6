# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

#include "csrrw_test.S"
#include "csrrwi_test.S"
#include "csrcs_test.S"
#include "csrcsi_test.S"

.globl main
main:
    #Start CSR tests: all tests
    #Handle exceptions
    la x6, exception_handler
    csrw mtvec, x6  ## Load the address of the exception handler into MTVEC
    csrw 0x341, x0  ## Writing Zero to MEPC CSR
    csrw 0x342, x0  ## Writing Zero to MCAUSE CSR
    #End Handle exceptions
    call csrrw
    call csrrwi
    call csrcs
    call csrcsi

    #End of csr test
    j csr_pass

csr_pass:
    li x1, 0xBEEFBEEF
    li x1, 0
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop: j self_loop

csr_fail:
    li x1, 0xBADBAD
    li x1, 1
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop_2: j self_loop_2

exception_handler:
    #addi x10, x10, 1  ##Increment number of exceptions
    li x1, 0xABCDEF
    csrr x3, 0x300
    srli x3, x3, 11
    andi x3, x3, 0b11
    li x8, 3
    li x9, 1
    beq x3, x8, machine_exception_handler
    #beqz x3, user_exception_handler
    #beq x3, x9, supervisor_exception_handler
    j csr_fail

machine_exception_handler:
    csrr x6, 0x300
    csrr x30, 0x341          ## Reading MEPC CSR which holds exception origin Address
    csrr x31, 0x342          ## Reading MCAUSE CSR which holds the cause of exception
    li x2 ,2                 ## MCAUSE == Illegal instruction
    beq x31, x2, goto_next_instr   ## Checking if exception is illegal instruction
    j csr_fail

goto_next_instr:
    csrw 0x342, 0		        ## Reseting MCAUSE value to 0 before handling new exception
    beq x30, x0, csr_fail
    addi x7, x30, 4
    jr x7			           ## Jump to latest instruction: MEPC + 4 Address location
    j csr_fail
