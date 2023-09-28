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
	# CSR_PMPADDR0
	li x3, 0xa5a5a5a5
	csrrw x14, 944, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x14, 944, x3
	li x3, 0xa5a5a5a4
	bne x3, x14, csr_fail
	li x3, 0x0783a3bf
	csrrw x14, 944, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x14, 944, x3
	li x3, 0x0783a3be
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x14, 944, x3
	li x3, 0xa7a7a7be
	bne x3, x14, csr_fail
	li x3, 0xa5313bdb
	csrrs x14, 944, x3
	li x3, 0xfffffffe
	bne x3, x14, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x14, 944, x3
	li x3, 0xfffffffe
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x14, 944, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	li x3, 0xb0729c10
	csrrc x14, 944, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrrwi x14, 944, 0b00101
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrrwi x14, 944, 0b11010
	li x3, 0x00000004
	bne x3, x14, csr_fail
	csrrwi x14, 944, 0b00010
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	csrrsi x14, 944, 0b00101
	li x3, 0x00000002
	bne x3, x14, csr_fail
	csrrsi x14, 944, 0b11010
	li x3, 0x00000006
	bne x3, x14, csr_fail
	csrrsi x14, 944, 0b00111
	li x3, 0x0000001e
	bne x3, x14, csr_fail
	csrrci x14, 944, 0b00101
	li x3, 0x0000001e
	bne x3, x14, csr_fail
	csrrci x14, 944, 0b11010
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	csrrci x14, 944, 0b10010
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrr x14, 944
	li x3, 0x00000000
	bne x3, x14, csr_fail
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


