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

	# CSR_PMPADDR6
	li x14, 0xa5a5a5a5
	csrrw x2, 950, x14
	li x14, 0x00000000
	bne x14, x2, csr_fail
	li x14, 0x5a5a5a5a
	csrrw x2, 950, x14
	li x14, 0xa5a5a5a4
	bne x14, x2, csr_fail
	li x14, 0xbda41260
	csrrw x2, 950, x14
	li x14, 0x5a5a5a5a
	bne x14, x2, csr_fail
	li x14, 0xa5a5a5a5
	csrrs x2, 950, x14
	li x14, 0xbda41260
	bne x14, x2, csr_fail
	li x14, 0x5a5a5a5a
	csrrs x2, 950, x14
	li x14, 0xbda5b7e4
	bne x14, x2, csr_fail
	li x14, 0x5df0e61a
	csrrs x2, 950, x14
	li x14, 0xfffffffe
	bne x14, x2, csr_fail
	li x14, 0xa5a5a5a5
	csrrc x2, 950, x14
	li x14, 0xfffffffe
	bne x14, x2, csr_fail
	li x14, 0x5a5a5a5a
	csrrc x2, 950, x14
	li x14, 0x5a5a5a5a
	bne x14, x2, csr_fail
	li x14, 0x28f157e4
	csrrc x2, 950, x14
	li x14, 0x00000000
	bne x14, x2, csr_fail
	csrrwi x2, 950, 0b00101
	li x14, 0x00000000
	bne x14, x2, csr_fail
	csrrwi x2, 950, 0b11010
	li x14, 0x00000004
	bne x14, x2, csr_fail
	csrrwi x2, 950, 0b01100
	li x14, 0x0000001a
	bne x14, x2, csr_fail
	csrrsi x2, 950, 0b00101
	li x14, 0x0000000c
	bne x14, x2, csr_fail
	csrrsi x2, 950, 0b11010
	li x14, 0x0000000c
	bne x14, x2, csr_fail
	csrrsi x2, 950, 0b10101
	li x14, 0x0000001e
	bne x14, x2, csr_fail
	csrrci x2, 950, 0b00101
	li x14, 0x0000001e
	bne x14, x2, csr_fail
	csrrci x2, 950, 0b11010
	li x14, 0x0000001a
	bne x14, x2, csr_fail
	csrrci x2, 950, 0b10001
	li x14, 0x00000000
	bne x14, x2, csr_fail
	csrr x2, 950
	li x14, 0x00000000
	bne x14, x2, csr_fail
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
