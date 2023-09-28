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

	# CSR_MSTATUS
	li x6, 0xFFFFFFFF
	csrrw x4, 768, x6
	li x6, 0x00000000
	bne x6, x4, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x4, 768, x6
	li x6, 0x8025a1a0
	bne x6, x4, csr_fail
	li x6, 0x6d11b01d
	csrrw x4, 768, x6
	li x6, 0x005a580a
	bne x6, x4, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x4, 768, x6
	li x6, 0x0011b008
	bne x6, x4, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x4, 768, x6
	li x6, 0x8035b1a8
	bne x6, x4, csr_fail
	li x6, 0x4eac03c8
	csrrs x4, 768, x6
	li x6, 0x807ff9aa
	bne x6, x4, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x4, 768, x6
	li x6, 0x807ff9aa
	bne x6, x4, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x4, 768, x6
	li x6, 0x005a580a
	bne x6, x4, csr_fail
	li x6, 0x05f68555
	csrrc x4, 768, x6
	li x6, 0x00000000
	bne x6, x4, csr_fail
	csrrwi x4, 768, 0b00101
	li x6, 0x00000000
	bne x6, x4, csr_fail
	csrrwi x4, 768, 0b11010
	li x6, 0x00000000
	bne x6, x4, csr_fail
	csrrwi x4, 768, 0b11010
	li x6, 0x0000000a
	bne x6, x4, csr_fail
	csrrsi x4, 768, 0b00101
	li x6, 0x0000000a
	bne x6, x4, csr_fail
	csrrsi x4, 768, 0b11010
	li x6, 0x0000000a
	bne x6, x4, csr_fail
	csrrsi x4, 768, 0b11111
	li x6, 0x0000000a
	bne x6, x4, csr_fail
	csrrci x4, 768, 0b00101
	li x6, 0x0000000a
	bne x6, x4, csr_fail
	csrrci x4, 768, 0b11010
	li x6, 0x0000000a
	bne x6, x4, csr_fail
	csrrci x4, 768, 0b11010
	li x6, 0x00000000
	bne x6, x4, csr_fail
	csrr x4, 768
	li x6, 0x00000000
	bne x6, x4, csr_fail
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


