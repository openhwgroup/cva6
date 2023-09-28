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
	# CSR_SSTATUS
	li x15, 0xa5a5a5a5
	csrrw x7, 256, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrw x7, 256, x15
	li x15, 0x00042120
	bne x15, x7, csr_fail
	li x15, 0xffbaa8bf
	csrrw x7, 256, x15
	li x15, 0x00084002
	bne x15, x7, csr_fail
	li x15, 0xa5a5a5a5
	csrrs x7, 256, x15
	li x15, 0x00082022
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrs x7, 256, x15
	li x15, 0x000c2122
	bne x15, x7, csr_fail
	li x15, 0x02fbaad0
	csrrs x7, 256, x15
	li x15, 0x000c6122
	bne x15, x7, csr_fail
	li x15, 0xa5a5a5a5
	csrrc x7, 256, x15
	li x15, 0x000c6122
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrc x7, 256, x15
	li x15, 0x00084002
	bne x15, x7, csr_fail
	li x15, 0x6058b29c
	csrrc x7, 256, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 256, 0b00101
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 256, 0b11010
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 256, 0b11100
	li x15, 0x00000002
	bne x15, x7, csr_fail
	csrrsi x7, 256, 0b00101
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrsi x7, 256, 0b11010
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrsi x7, 256, 0b00000
	li x15, 0x00000002
	bne x15, x7, csr_fail
	csrrci x7, 256, 0b00101
	li x15, 0x00000002
	bne x15, x7, csr_fail
	csrrci x7, 256, 0b11010
	li x15, 0x00000002
	bne x15, x7, csr_fail
	csrrci x7, 256, 0b00110
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrr x7, 256
	li x15, 0x00000000
	bne x15, x7, csr_fail
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


