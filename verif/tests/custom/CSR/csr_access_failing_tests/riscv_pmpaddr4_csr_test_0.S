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
RVMODEL_BOOT

	# CSR_PMPADDR4
	li x3, 0xa5a5a5a5
	csrrw x12, 948, x3
	li x3, 0x00000000
	bne x3, x12, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x12, 948, x3
	li x3, 0xa5a5a5a4
	bne x3, x12, csr_fail
	li x3, 0x8386e3a1
	csrrw x12, 948, x3
	li x3, 0x5a5a5a5a
	bne x3, x12, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x12, 948, x3
	li x3, 0x8386e3a0
	bne x3, x12, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x12, 948, x3
	li x3, 0xa7a7e7a4
	bne x3, x12, csr_fail
	li x3, 0x20406d1a
	csrrs x12, 948, x3
	li x3, 0xfffffffe
	bne x3, x12, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x12, 948, x3
	li x3, 0xfffffffe
	bne x3, x12, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x12, 948, x3
	li x3, 0x5a5a5a5a
	bne x3, x12, csr_fail
	li x3, 0xa39f6193
	csrrc x12, 948, x3
	li x3, 0x00000000
	bne x3, x12, csr_fail
	csrrwi x12, 948, 0b00101
	li x3, 0x00000000
	bne x3, x12, csr_fail
	csrrwi x12, 948, 0b11010
	li x3, 0x00000004
	bne x3, x12, csr_fail
	csrrwi x12, 948, 0b10001
	li x3, 0x0000001a
	bne x3, x12, csr_fail
	csrrsi x12, 948, 0b00101
	li x3, 0x00000010
	bne x3, x12, csr_fail
	csrrsi x12, 948, 0b11010
	li x3, 0x00000014
	bne x3, x12, csr_fail
	csrrsi x12, 948, 0b10110
	li x3, 0x0000001e
	bne x3, x12, csr_fail
	csrrci x12, 948, 0b00101
	li x3, 0x0000001e
	bne x3, x12, csr_fail
	csrrci x12, 948, 0b11010
	li x3, 0x0000001a
	bne x3, x12, csr_fail
	csrrci x12, 948, 0b00100
	li x3, 0x00000000
	bne x3, x12, csr_fail
	csrr x12, 948
	li x3, 0x00000000
	bne x3, x12, csr_fail
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
