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

	# CSR_PMPADDR3
	li x7, 0xa5a5a5a5
	csrrw x11, 947, x7
	li x7, 0x00000000
	bne x7, x11, csr_fail
	li x7, 0x5a5a5a5a
	csrrw x11, 947, x7
	li x7, 0xa5a5a5a4
	bne x7, x11, csr_fail
	li x7, 0x71a0ad7b
	csrrw x11, 947, x7
	li x7, 0x5a5a5a5a
	bne x7, x11, csr_fail
	li x7, 0xa5a5a5a5
	csrrs x11, 947, x7
	li x7, 0x71a0ad7a
	bne x7, x11, csr_fail
	li x7, 0x5a5a5a5a
	csrrs x11, 947, x7
	li x7, 0xf5a5adfe
	bne x7, x11, csr_fail
	li x7, 0x7e1bbfe7
	csrrs x11, 947, x7
	li x7, 0xfffffffe
	bne x7, x11, csr_fail
	li x7, 0xa5a5a5a5
	csrrc x11, 947, x7
	li x7, 0xfffffffe
	bne x7, x11, csr_fail
	li x7, 0x5a5a5a5a
	csrrc x11, 947, x7
	li x7, 0x5a5a5a5a
	bne x7, x11, csr_fail
	li x7, 0x313f8057
	csrrc x11, 947, x7
	li x7, 0x00000000
	bne x7, x11, csr_fail
	csrrwi x11, 947, 0b00101
	li x7, 0x00000000
	bne x7, x11, csr_fail
	csrrwi x11, 947, 0b11010
	li x7, 0x00000004
	bne x7, x11, csr_fail
	csrrwi x11, 947, 0b11101
	li x7, 0x0000001a
	bne x7, x11, csr_fail
	csrrsi x11, 947, 0b00101
	li x7, 0x0000001c
	bne x7, x11, csr_fail
	csrrsi x11, 947, 0b11010
	li x7, 0x0000001c
	bne x7, x11, csr_fail
	csrrsi x11, 947, 0b00000
	li x7, 0x0000001e
	bne x7, x11, csr_fail
	csrrci x11, 947, 0b00101
	li x7, 0x0000001e
	bne x7, x11, csr_fail
	csrrci x11, 947, 0b11010
	li x7, 0x0000001a
	bne x7, x11, csr_fail
	csrrci x11, 947, 0b00111
	li x7, 0x00000000
	bne x7, x11, csr_fail
	csrr x11, 947
	li x7, 0x00000000
	bne x7, x11, csr_fail
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
