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

	# CSR_PMPADDR2
	li x14, 0xa5a5a5a5
	csrrw x15, 946, x14
	li x14, 0x00000000
	bne x14, x15, csr_fail
	li x14, 0x5a5a5a5a
	csrrw x15, 946, x14
	li x14, 0xa5a5a5a4
	bne x14, x15, csr_fail
	li x14, 0x94154ed1
	csrrw x15, 946, x14
	li x14, 0x5a5a5a5a
	bne x14, x15, csr_fail
	li x14, 0xa5a5a5a5
	csrrs x15, 946, x14
	li x14, 0x94154ed0
	bne x14, x15, csr_fail
	li x14, 0x5a5a5a5a
	csrrs x15, 946, x14
	li x14, 0xb5b5eff4
	bne x14, x15, csr_fail
	li x14, 0x345b61a0
	csrrs x15, 946, x14
	li x14, 0xfffffffe
	bne x14, x15, csr_fail
	li x14, 0xa5a5a5a5
	csrrc x15, 946, x14
	li x14, 0xfffffffe
	bne x14, x15, csr_fail
	li x14, 0x5a5a5a5a
	csrrc x15, 946, x14
	li x14, 0x5a5a5a5a
	bne x14, x15, csr_fail
	li x14, 0x970406f6
	csrrc x15, 946, x14
	li x14, 0x00000000
	bne x14, x15, csr_fail
	csrrwi x15, 946, 0b00101
	li x14, 0x00000000
	bne x14, x15, csr_fail
	csrrwi x15, 946, 0b11010
	li x14, 0x00000004
	bne x14, x15, csr_fail
	csrrwi x15, 946, 0b10100
	li x14, 0x0000001a
	bne x14, x15, csr_fail
	csrrsi x15, 946, 0b00101
	li x14, 0x00000014
	bne x14, x15, csr_fail
	csrrsi x15, 946, 0b11010
	li x14, 0x00000014
	bne x14, x15, csr_fail
	csrrsi x15, 946, 0b01111
	li x14, 0x0000001e
	bne x14, x15, csr_fail
	csrrci x15, 946, 0b00101
	li x14, 0x0000001e
	bne x14, x15, csr_fail
	csrrci x15, 946, 0b11010
	li x14, 0x0000001a
	bne x14, x15, csr_fail
	csrrci x15, 946, 0b10001
	li x14, 0x00000000
	bne x14, x15, csr_fail
	csrr x15, 946
	li x14, 0x00000000
	bne x14, x15, csr_fail
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
