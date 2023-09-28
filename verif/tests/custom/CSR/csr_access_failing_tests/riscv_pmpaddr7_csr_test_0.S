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

	# CSR_PMPADDR7
	li x5, 0xa5a5a5a5
	csrrw x15, 951, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x15, 951, x5
	li x5, 0xa5a5a5a4
	bne x5, x15, csr_fail
	li x5, 0x5ed59bfd
	csrrw x15, 951, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x15, 951, x5
	li x5, 0x5ed59bfc
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x15, 951, x5
	li x5, 0xfff5bffc
	bne x5, x15, csr_fail
	li x5, 0x0628e3f0
	csrrs x15, 951, x5
	li x5, 0xfffffffe
	bne x5, x15, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x15, 951, x5
	li x5, 0xfffffffe
	bne x5, x15, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x15, 951, x5
	li x5, 0x5a5a5a5a
	bne x5, x15, csr_fail
	li x5, 0x58e5c2e8
	csrrc x15, 951, x5
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 951, 0b00101
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrrwi x15, 951, 0b11010
	li x5, 0x00000004
	bne x5, x15, csr_fail
	csrrwi x15, 951, 0b11101
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrsi x15, 951, 0b00101
	li x5, 0x0000001c
	bne x5, x15, csr_fail
	csrrsi x15, 951, 0b11010
	li x5, 0x0000001c
	bne x5, x15, csr_fail
	csrrsi x15, 951, 0b10000
	li x5, 0x0000001e
	bne x5, x15, csr_fail
	csrrci x15, 951, 0b00101
	li x5, 0x0000001e
	bne x5, x15, csr_fail
	csrrci x15, 951, 0b11010
	li x5, 0x0000001a
	bne x5, x15, csr_fail
	csrrci x15, 951, 0b01000
	li x5, 0x00000000
	bne x5, x15, csr_fail
	csrr x15, 951
	li x5, 0x00000000
	bne x5, x15, csr_fail
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
