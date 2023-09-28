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
	# CSR_PMPADDR1
	li x1, 0xa5a5a5a5
	csrrw x2, 945, x1
	li x1, 0x00000000
	bne x1, x2, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x2, 945, x1
	li x1, 0xa5a5a5a4
	bne x1, x2, csr_fail
	li x1, 0x4329bde7
	csrrw x2, 945, x1
	li x1, 0x5a5a5a5a
	bne x1, x2, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x2, 945, x1
	li x1, 0x4329bde6
	bne x1, x2, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x2, 945, x1
	li x1, 0xe7adbde6
	bne x1, x2, csr_fail
	li x1, 0x53bc8131
	csrrs x2, 945, x1
	li x1, 0xfffffffe
	bne x1, x2, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x2, 945, x1
	li x1, 0xfffffffe
	bne x1, x2, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x2, 945, x1
	li x1, 0x5a5a5a5a
	bne x1, x2, csr_fail
	li x1, 0x51b45d81
	csrrc x2, 945, x1
	li x1, 0x00000000
	bne x1, x2, csr_fail
	csrrwi x2, 945, 0b00101
	li x1, 0x00000000
	bne x1, x2, csr_fail
	csrrwi x2, 945, 0b11010
	li x1, 0x00000004
	bne x1, x2, csr_fail
	csrrwi x2, 945, 0b01011
	li x1, 0x0000001a
	bne x1, x2, csr_fail
	csrrsi x2, 945, 0b00101
	li x1, 0x0000000a
	bne x1, x2, csr_fail
	csrrsi x2, 945, 0b11010
	li x1, 0x0000000e
	bne x1, x2, csr_fail
	csrrsi x2, 945, 0b11100
	li x1, 0x0000001e
	bne x1, x2, csr_fail
	csrrci x2, 945, 0b00101
	li x1, 0x0000001e
	bne x1, x2, csr_fail
	csrrci x2, 945, 0b11010
	li x1, 0x0000001a
	bne x1, x2, csr_fail
	csrrci x2, 945, 0b00001
	li x1, 0x00000000
	bne x1, x2, csr_fail
	csrr x2, 945
	li x1, 0x00000000
	bne x1, x2, csr_fail
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
