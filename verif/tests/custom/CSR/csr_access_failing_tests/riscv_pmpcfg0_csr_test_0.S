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
	# CSR_PMPCFG0
	li x1, 0xa5a5a5a5
	csrrw x8, 928, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 928, x1
	li x1, 0xa5a5a5a5
	bne x1, x8, csr_fail
	li x1, 0x7a6e1dbc
	csrrw x8, 928, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 928, x1
	li x1, 0x7a6e1dbc
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 928, x1
	li x1, 0xffefbdbd
	bne x1, x8, csr_fail
	li x1, 0x89f80ecc
	csrrs x8, 928, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 928, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 928, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0x045d23c7
	csrrc x8, 928, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 928, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 928, 0b11010
	li x1, 0x00000005
	bne x1, x8, csr_fail
	csrrwi x8, 928, 0b10111
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrsi x8, 928, 0b00101
	li x1, 0x00000017
	bne x1, x8, csr_fail
	csrrsi x8, 928, 0b11010
	li x1, 0x00000017
	bne x1, x8, csr_fail
	csrrsi x8, 928, 0b00100
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 928, 0b00101
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 928, 0b11010
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrci x8, 928, 0b00001
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrr x8, 928
	li x1, 0x00000000
	bne x1, x8, csr_fail
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
