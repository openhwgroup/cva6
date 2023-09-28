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

	# CSR_PMPCFG1
	li x3, 0xa5a5a5a5
	csrrw x9, 929, x3
	li x3, 0x00000000
	bne x3, x9, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x9, 929, x3
	li x3, 0xa5a5a5a5
	bne x3, x9, csr_fail
	li x3, 0xdf7a99f3
	csrrw x9, 929, x3
	li x3, 0x5a5a5a5a
	bne x3, x9, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x9, 929, x3
	li x3, 0xdf7a99f3
	bne x3, x9, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x9, 929, x3
	li x3, 0xffffbdf7
	bne x3, x9, csr_fail
	li x3, 0xa3347281
	csrrs x9, 929, x3
	li x3, 0xffffffff
	bne x3, x9, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x9, 929, x3
	li x3, 0xffffffff
	bne x3, x9, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x9, 929, x3
	li x3, 0x5a5a5a5a
	bne x3, x9, csr_fail
	li x3, 0x95109abd
	csrrc x9, 929, x3
	li x3, 0x00000000
	bne x3, x9, csr_fail
	csrrwi x9, 929, 0b00101
	li x3, 0x00000000
	bne x3, x9, csr_fail
	csrrwi x9, 929, 0b11010
	li x3, 0x00000005
	bne x3, x9, csr_fail
	csrrwi x9, 929, 0b11000
	li x3, 0x0000001a
	bne x3, x9, csr_fail
	csrrsi x9, 929, 0b00101
	li x3, 0x00000018
	bne x3, x9, csr_fail
	csrrsi x9, 929, 0b11010
	li x3, 0x0000001d
	bne x3, x9, csr_fail
	csrrsi x9, 929, 0b01011
	li x3, 0x0000001f
	bne x3, x9, csr_fail
	csrrci x9, 929, 0b00101
	li x3, 0x0000001f
	bne x3, x9, csr_fail
	csrrci x9, 929, 0b11010
	li x3, 0x0000001a
	bne x3, x9, csr_fail
	csrrci x9, 929, 0b00111
	li x3, 0x00000000
	bne x3, x9, csr_fail
	csrr x9, 929
	li x3, 0x00000000
	bne x3, x9, csr_fail
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
