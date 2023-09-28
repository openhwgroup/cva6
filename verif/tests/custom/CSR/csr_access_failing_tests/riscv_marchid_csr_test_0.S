// Copyright 2023 Thales
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

#include "model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
	la x6, exception_handler  
        csrw mtvec, x6  ## Load the address of the exception handler into MTVEC
	csrw 0x341, x0
    	csrw 0x342, x0

	# CSR_MARCHID
	csrr x31, 3858
	li x6, 0x00000003
	bne x31, x4, csr_fail
	li x4, 0xa5a5a5a5
	csrrw x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	li x4, 0x5a5a5a5a
	csrrw x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	li x4, 0x82cebeaf
	csrrw x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	li x4, 0xa5a5a5a5
	csrrs x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	li x4, 0x5a5a5a5a
	csrrs x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	li x4, 0xd6ecdb19
	csrrs x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	li x4, 0xa5a5a5a5
	csrrc x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	li x4, 0x5a5a5a5a
	csrrc x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	li x4, 0x6a7b6028
	csrrc x14, 3858, x4
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrwi x14, 3858, 0b00101
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrwi x14, 3858, 0b11010
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrwi x14, 3858, 0b01001
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrsi x14, 3858, 0b00101
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrsi x14, 3858, 0b11010
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrsi x14, 3858, 0b01110
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrci x14, 3858, 0b00101
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrci x14, 3858, 0b11010
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrrci x14, 3858, 0b10110
	li x4, 0x00000003
	bne x4, x14, csr_fail
	csrr x14, 3858
	li x4, 0x00000003
	bne x4, x14, csr_fail

	j csr_pass

exception_handler:
csrr x30, 0x341	    ## Reading MEPC CSR which holds exception origin Address		
csrr x31, 0x342     ## Reading MCAUSE CSR which holds the cause of exception
addi x2, x2,2
beq x31, x2, next   ## Checking is exception is expected exception or not
j csr_fail

next:
addi x1, x1, 0
bne x30, x1, next_iter  ## If MEPC has non-zero value then jump to next_iter
j csr_fail

next_iter:
li x2, 0 		## Initilizing 0 in x2 register where MCAUSE value is previously stored
addi x7, x30, 4
jr x7			## Jump to MEPC + 4 Address location



csr_pass:
	li x1, 0
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, t5
	self_loop: j self_loop

csr_fail:
	li x1, 1
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, t5
	self_loop_2: j self_loop_2

RVMODEL_DATA_BEGIN
RVMODEL_DATA_END
