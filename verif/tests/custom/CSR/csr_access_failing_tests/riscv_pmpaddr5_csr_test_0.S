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

	# CSR_PMPADDR5
	li x2, 0xa5a5a5a5
	csrrw x12, 949, x2
	li x2, 0x00000000
	bne x2, x12, csr_fail
	li x2, 0x5a5a5a5a
	csrrw x12, 949, x2
	li x2, 0xa5a5a5a4
	bne x2, x12, csr_fail
	li x2, 0x2b7f410f
	csrrw x12, 949, x2
	li x2, 0x5a5a5a5a
	bne x2, x12, csr_fail
	li x2, 0xa5a5a5a5
	csrrs x12, 949, x2
	li x2, 0x2b7f410e
	bne x2, x12, csr_fail
	li x2, 0x5a5a5a5a
	csrrs x12, 949, x2
	li x2, 0xafffe5ae
	bne x2, x12, csr_fail
	li x2, 0x0fc944fe
	csrrs x12, 949, x2
	li x2, 0xfffffffe
	bne x2, x12, csr_fail
	li x2, 0xa5a5a5a5
	csrrc x12, 949, x2
	li x2, 0xfffffffe
	bne x2, x12, csr_fail
	li x2, 0x5a5a5a5a
	csrrc x12, 949, x2
	li x2, 0x5a5a5a5a
	bne x2, x12, csr_fail
	li x2, 0xb74dfaa6
	csrrc x12, 949, x2
	li x2, 0x00000000
	bne x2, x12, csr_fail
	csrrwi x12, 949, 0b00101
	li x2, 0x00000000
	bne x2, x12, csr_fail
	csrrwi x12, 949, 0b11010
	li x2, 0x00000004
	bne x2, x12, csr_fail
	csrrwi x12, 949, 0b10000
	li x2, 0x0000001a
	bne x2, x12, csr_fail
	csrrsi x12, 949, 0b00101
	li x2, 0x00000010
	bne x2, x12, csr_fail
	csrrsi x12, 949, 0b11010
	li x2, 0x00000014
	bne x2, x12, csr_fail
	csrrsi x12, 949, 0b11100
	li x2, 0x0000001e
	bne x2, x12, csr_fail
	csrrci x12, 949, 0b00101
	li x2, 0x0000001e
	bne x2, x12, csr_fail
	csrrci x12, 949, 0b11010
	li x2, 0x0000001a
	bne x2, x12, csr_fail
	csrrci x12, 949, 0b10111
	li x2, 0x00000000
	bne x2, x12, csr_fail
	csrr x12, 949
	li x2, 0x00000000
	bne x2, x12, csr_fail
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
