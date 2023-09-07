#include "model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
RVMODEL_BOOT
	# CSR_MSCRATCH
	li x10, 0xa5a5a5a5
	csrrw x14, 0x340, x10
	li x10, 0x00000000
	bne x10, x14, csr_fail
	li x10, 0x5a5a5a5a
	csrrw x14, 0x340, x10
	li x10, 0xa5a5a5a5
	bne x10, x14, csr_fail
	li x10, 0x6c218674
	csrrw x14, 0x340, x10
	li x10, 0x5a5a5a5a
	bne x10, x14, csr_fail
	li x10, 0xa5a5a5a5
	csrrs x14, 0x340, x10
	li x10, 0x6c218674
	bne x10, x14, csr_fail
	li x10, 0x5a5a5a5a
	csrrs x14, 0x340, x10
	li x10, 0xeda5a7f5
	bne x10, x14, csr_fail
	li x10, 0xdd2d25a6
	csrrs x14, 0x340, x10
	li x10, 0xffffffff
	bne x10, x14, csr_fail
	li x10, 0xa5a5a5a5
	csrrc x14, 0x340, x10
	li x10, 0xffffffff
	bne x10, x14, csr_fail
	li x10, 0x5a5a5a5a
	csrrc x14, 0x340, x10
	li x10, 0x5a5a5a5a
	bne x10, x14, csr_fail
	li x10, 0x8959179c
	csrrc x14, 0x340, x10
	li x10, 0x00000000
	bne x10, x14, csr_fail
	csrrwi x14, 0x340, 0b00101
	li x10, 0x00000000
	bne x10, x14, csr_fail
	csrrwi x14, 0x340, 0b11010
	li x10, 0x00000005
	bne x10, x14, csr_fail
	csrrwi x14, 0x340, 0b01110
	li x10, 0x0000001a
	bne x10, x14, csr_fail
	csrrsi x14, 0x340, 0b00101
	li x10, 0x0000000e
	bne x10, x14, csr_fail
	csrrsi x14, 0x340, 0b11010
	li x10, 0x0000000f
	bne x10, x14, csr_fail
	csrrsi x14, 0x340, 0b00000
	li x10, 0x0000001f
	bne x10, x14, csr_fail
	csrrci x14, 0x340, 0b00101
	li x10, 0x0000001f
	bne x10, x14, csr_fail
	csrrci x14, 0x340, 0b11010
	li x10, 0x0000001a
	bne x10, x14, csr_fail
	csrrci x14, 0x340, 0b00100
	li x10, 0x00000000
	bne x10, x14, csr_fail
	csrr x14, 0x340
	li x10, 0x00000000
	bne x10, x14, csr_fail
csr_pass:
	li x1, 0
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, x30
	self_loop: j self_loop

csr_fail:
	li x1, 1
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, x30
	self_loop_2: j self_loop_2

RVMODEL_DATA_BEGIN
RVMODEL_DATA_END
