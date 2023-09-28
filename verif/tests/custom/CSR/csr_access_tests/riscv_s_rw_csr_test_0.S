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
	la x6, exception_handler  
        csrw mtvec, x6  ## Load the address of the exception handler into MTVEC

	csrw 0x341, x0  ## Writing Zero to MEPC CSR
    	csrw 0x342, x0  ## Writing Zero to MCAUSE CSR

	li x1, 0x222
	csrw 0x303, x1  ## Configuring MIDELEG CSR 

	# CSR_SIE
	li x5, 0xa5a5a5a5
	csrrw x4, 260, x5
	li x5, 0x00000000
	bne x5, x4, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x4, 260, x5
	li x5, 0x00000020
	bne x5, x4, csr_fail
	li x5, 0xe4ca5ed3
	csrrw x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	li x5, 0x66c2984c
	csrrs x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	li x5, 0x9d619640
	csrrc x4, 260, x5
	li x5, 0x00000000
	bne x5, x4, csr_fail
	csrrwi x4, 260, 0b00101
	li x5, 0x00000000
	bne x5, x4, csr_fail
	csrrwi x4, 260, 0b11010
	li x5, 0x00000000
	bne x5, x4, csr_fail
	csrrwi x4, 260, 0b00110
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrsi x4, 260, 0b00101
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrsi x4, 260, 0b11010
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrsi x4, 260, 0b01100
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrci x4, 260, 0b00101
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrci x4, 260, 0b11010
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrci x4, 260, 0b10001
	li x5, 0x00000000
	bne x5, x4, csr_fail
	csrr x4, 260
	li x5, 0x00000000
	bne x5, x4, csr_fail

	# CSR_STVEC
	li x7, 0xa5a5a5a5
	csrrw x1, 261, x7
	li x7, 0x00000000
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrw x1, 261, x7
	li x7, 0xa5a5a5a5
	bne x7, x1, csr_fail
	li x7, 0xd2ec680e
	csrrw x1, 261, x7
	li x7, 0x5a5a5a58
	bne x7, x1, csr_fail
	li x7, 0xa5a5a5a5
	csrrs x1, 261, x7
	li x7, 0xd2ec680c
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrs x1, 261, x7
	li x7, 0xf7ededad
	bne x7, x1, csr_fail
	li x7, 0x14191a03
	csrrs x1, 261, x7
	li x7, 0xfffffffd
	bne x7, x1, csr_fail
	li x7, 0xa5a5a5a5
	csrrc x1, 261, x7
	li x7, 0xfffffffd
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrc x1, 261, x7
	li x7, 0x5a5a5a58
	bne x7, x1, csr_fail
	li x7, 0x9f73bde0
	csrrc x1, 261, x7
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b00101
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b11010
	li x7, 0x00000005
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b01011
	li x7, 0x00000018
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b00101
	li x7, 0x00000009
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b11010
	li x7, 0x0000000d
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b00111
	li x7, 0x0000001d
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b00101
	li x7, 0x0000001d
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b11010
	li x7, 0x00000018
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b11010
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrr x1, 261
	li x7, 0x00000000
	bne x7, x1, csr_fail


	# CSR_SSCRATCH
	li x1, 0xa5a5a5a5
	csrrw x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x3, 320, x1
	li x1, 0xa5a5a5a5
	bne x1, x3, csr_fail
	li x1, 0xf149b7e8
	csrrw x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x3, 320, x1
	li x1, 0xf149b7e8
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x3, 320, x1
	li x1, 0xf5edb7ed
	bne x1, x3, csr_fail
	li x1, 0xbcc8c1c2
	csrrs x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	li x1, 0x18fd947a
	csrrc x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b00101
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b11010
	li x1, 0x00000005
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b01010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b00101
	li x1, 0x0000000a
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b11010
	li x1, 0x0000000f
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b10100
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b00101
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b11010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b00001
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrr x3, 320
	li x1, 0x00000000
	bne x1, x3, csr_fail


	# CSR_SEPC
	li x12, 0xa5a5a5a5
	csrrw x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x6, 321, x12
	li x12, 0xa5a5a5a4
	bne x12, x6, csr_fail
	li x12, 0x7a6c28e1
	csrrw x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x6, 321, x12
	li x12, 0x7a6c28e0
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x6, 321, x12
	li x12, 0xffedade4
	bne x12, x6, csr_fail
	li x12, 0x1228d835
	csrrs x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	li x12, 0x712201a4
	csrrc x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b00101
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b11010
	li x12, 0x00000004
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b00010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b00101
	li x12, 0x00000002
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b11010
	li x12, 0x00000006
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b01001
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b00101
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b11010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b11110
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrr x6, 321
	li x12, 0x00000000
	bne x12, x6, csr_fail

	# CSR_SCAUSE
	li x4, 0xa5a5a5a5
	csrrw x7, 322, x4
	li x4, 0x00000000
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrw x7, 322, x4
	li x4, 0xa5a5a5a5
	bne x4, x7, csr_fail
	li x4, 0x8b85f3c8
	csrrw x7, 322, x4
	li x4, 0x5a5a5a5a
	bne x4, x7, csr_fail
	li x4, 0xa5a5a5a5
	csrrs x7, 322, x4
	li x4, 0x8b85f3c8
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrs x7, 322, x4
	li x4, 0xafa5f7ed
	bne x4, x7, csr_fail
	li x4, 0x20fff1ae
	csrrs x7, 322, x4
	li x4, 0xffffffff
	bne x4, x7, csr_fail
	li x4, 0xa5a5a5a5
	csrrc x7, 322, x4
	li x4, 0xffffffff
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrc x7, 322, x4
	li x4, 0x5a5a5a5a
	bne x4, x7, csr_fail
	li x4, 0x1ee47ee4
	csrrc x7, 322, x4
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b00101
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b11010
	li x4, 0x00000005
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b11111
	li x4, 0x0000001a
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b00101
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b11010
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b00111
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b00101
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b11010
	li x4, 0x0000001a
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b10110
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrr x7, 322
	li x4, 0x00000000
	bne x4, x7, csr_fail

	# CSR_STVAL
	li x15, 0xa5a5a5a5
	csrrw x7, 323, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrw x7, 323, x15
	li x15, 0xa5a5a5a5
	bne x15, x7, csr_fail
	li x15, 0x195a0d46
	csrrw x7, 323, x15
	li x15, 0x5a5a5a5a
	bne x15, x7, csr_fail
	li x15, 0xa5a5a5a5
	csrrs x7, 323, x15
	li x15, 0x195a0d46
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrs x7, 323, x15
	li x15, 0xbdffade7
	bne x15, x7, csr_fail
	li x15, 0xe82c2396
	csrrs x7, 323, x15
	li x15, 0xffffffff
	bne x15, x7, csr_fail
	li x15, 0xa5a5a5a5
	csrrc x7, 323, x15
	li x15, 0xffffffff
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrc x7, 323, x15
	li x15, 0x5a5a5a5a
	bne x15, x7, csr_fail
	li x15, 0x3fc5b750
	csrrc x7, 323, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b00101
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b11010
	li x15, 0x00000005
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b00110
	li x15, 0x0000001a
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b00101
	li x15, 0x00000006
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b11010
	li x15, 0x00000007
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b00110
	li x15, 0x0000001f
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b00101
	li x15, 0x0000001f
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b11010
	li x15, 0x0000001a
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b00010
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrr x7, 323
	li x15, 0x00000000
	bne x15, x7, csr_fail

	j supervisor_mode_code_start
	j csr_fail

supervisor_mode_code_start:
	csrw  0x341, 0    ## Writing zero into MEPC CSR
	csrw  0x342, 0    ## Reading Zero into MCAUSE CSR

## Configuring PMP CSRs	
	## set start address range t0 x7
 	la x7, supervisor_code
 	li x28, 0x10000
 	add x7, x7, x28
 	# Enable R,W,X,TOR IN PMPCFG CSR t0 x8
 	li x8, 0x0F
	#set PMPADDR0 CSR with x7
 	csrw 0x3B0, x7
	# set PMPCFG0 CSR with x8
 	csrw 0x3A0, x8

## Configuring MSTATUS MPP bit to 01(supervisor mode)
	# Save the current mode in x28
        csrr x28, 0x300
        # Set the MPP field to supervisor mode (1)
        li x29, 0b1
        slli x29, x29, 11
        addi x28, x29, 0
        # Write the modified MSTATUS value back to the CSR
        csrw 0x300, x28
## Assigning supervisor code starting PC value to MEPC CSR	
	la x28, supervisor_code
        csrw 0x341, x28
	csrr x31, 0x300
       	mret
      
# Supervisor code starts here
supervisor_code:

	# CSR_SIE
	li x5, 0xa5a5a5a5
	csrrw x4, 260, x5
	li x5, 0x00000000
	bne x5, x4, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x4, 260, x5
	li x5, 0x00000020
	bne x5, x4, csr_fail
	li x5, 0xe4ca5ed3
	csrrw x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	li x5, 0x66c2984c
	csrrs x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	li x5, 0x9d619640
	csrrc x4, 260, x5
	li x5, 0x00000000
	bne x5, x4, csr_fail
	csrrwi x4, 260, 0b00101
	li x5, 0x00000000
	bne x5, x4, csr_fail
	csrrwi x4, 260, 0b11010
	li x5, 0x00000000
	bne x5, x4, csr_fail
	csrrwi x4, 260, 0b00110
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrsi x4, 260, 0b00101
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrsi x4, 260, 0b11010
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrsi x4, 260, 0b01100
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrci x4, 260, 0b00101
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrci x4, 260, 0b11010
	li x5, 0x00000002
	bne x5, x4, csr_fail
	csrrci x4, 260, 0b10001
	li x5, 0x00000000
	bne x5, x4, csr_fail
	csrr x4, 260
	li x5, 0x00000000
	bne x5, x4, csr_fail


	# CSR_STVEC
	li x7, 0xa5a5a5a5
	csrrw x1, 261, x7
	li x7, 0x00000000
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrw x1, 261, x7
	li x7, 0xa5a5a5a5
	bne x7, x1, csr_fail
	li x7, 0xd2ec680e
	csrrw x1, 261, x7
	li x7, 0x5a5a5a58
	bne x7, x1, csr_fail
	li x7, 0xa5a5a5a5
	csrrs x1, 261, x7
	li x7, 0xd2ec680c
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrs x1, 261, x7
	li x7, 0xf7ededad
	bne x7, x1, csr_fail
	li x7, 0x14191a03
	csrrs x1, 261, x7
	li x7, 0xfffffffd
	bne x7, x1, csr_fail
	li x7, 0xa5a5a5a5
	csrrc x1, 261, x7
	li x7, 0xfffffffd
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrc x1, 261, x7
	li x7, 0x5a5a5a58
	bne x7, x1, csr_fail
	li x7, 0x9f73bde0
	csrrc x1, 261, x7
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b00101
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b11010
	li x7, 0x00000005
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b01011
	li x7, 0x00000018
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b00101
	li x7, 0x00000009
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b11010
	li x7, 0x0000000d
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b00111
	li x7, 0x0000001d
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b00101
	li x7, 0x0000001d
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b11010
	li x7, 0x00000018
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b11010
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrr x1, 261
	li x7, 0x00000000
	bne x7, x1, csr_fail	
	
	# CSR_SSCRATCH
	li x1, 0xa5a5a5a5
	csrrw x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x3, 320, x1
	li x1, 0xa5a5a5a5
	bne x1, x3, csr_fail
	li x1, 0xf149b7e8
	csrrw x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x3, 320, x1
	li x1, 0xf149b7e8
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x3, 320, x1
	li x1, 0xf5edb7ed
	bne x1, x3, csr_fail
	li x1, 0xbcc8c1c2
	csrrs x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	li x1, 0x18fd947a
	csrrc x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b00101
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b11010
	li x1, 0x00000005
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b01010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b00101
	li x1, 0x0000000a
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b11010
	li x1, 0x0000000f
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b10100
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b00101
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b11010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b00001
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrr x3, 320
	li x1, 0x00000000
	bne x1, x3, csr_fail


	# CSR_SEPC
	li x12, 0xa5a5a5a5
	csrrw x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x6, 321, x12
	li x12, 0xa5a5a5a4
	bne x12, x6, csr_fail
	li x12, 0x7a6c28e1
	csrrw x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x6, 321, x12
	li x12, 0x7a6c28e0
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x6, 321, x12
	li x12, 0xffedade4
	bne x12, x6, csr_fail
	li x12, 0x1228d835
	csrrs x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	li x12, 0x712201a4
	csrrc x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b00101
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b11010
	li x12, 0x00000004
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b00010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b00101
	li x12, 0x00000002
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b11010
	li x12, 0x00000006
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b01001
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b00101
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b11010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b11110
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrr x6, 321
	li x12, 0x00000000
	bne x12, x6, csr_fail

	# CSR_SCAUSE
	li x4, 0xa5a5a5a5
	csrrw x7, 322, x4
	li x4, 0x00000000
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrw x7, 322, x4
	li x4, 0xa5a5a5a5
	bne x4, x7, csr_fail
	li x4, 0x8b85f3c8
	csrrw x7, 322, x4
	li x4, 0x5a5a5a5a
	bne x4, x7, csr_fail
	li x4, 0xa5a5a5a5
	csrrs x7, 322, x4
	li x4, 0x8b85f3c8
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrs x7, 322, x4
	li x4, 0xafa5f7ed
	bne x4, x7, csr_fail
	li x4, 0x20fff1ae
	csrrs x7, 322, x4
	li x4, 0xffffffff
	bne x4, x7, csr_fail
	li x4, 0xa5a5a5a5
	csrrc x7, 322, x4
	li x4, 0xffffffff
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrc x7, 322, x4
	li x4, 0x5a5a5a5a
	bne x4, x7, csr_fail
	li x4, 0x1ee47ee4
	csrrc x7, 322, x4
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b00101
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b11010
	li x4, 0x00000005
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b11111
	li x4, 0x0000001a
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b00101
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b11010
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b00111
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b00101
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b11010
	li x4, 0x0000001a
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b10110
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrr x7, 322
	li x4, 0x00000000
	bne x4, x7, csr_fail

	# CSR_STVAL
	li x15, 0xa5a5a5a5
	csrrw x7, 323, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrw x7, 323, x15
	li x15, 0xa5a5a5a5
	bne x15, x7, csr_fail
	li x15, 0x195a0d46
	csrrw x7, 323, x15
	li x15, 0x5a5a5a5a
	bne x15, x7, csr_fail
	li x15, 0xa5a5a5a5
	csrrs x7, 323, x15
	li x15, 0x195a0d46
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrs x7, 323, x15
	li x15, 0xbdffade7
	bne x15, x7, csr_fail
	li x15, 0xe82c2396
	csrrs x7, 323, x15
	li x15, 0xffffffff
	bne x15, x7, csr_fail
	li x15, 0xa5a5a5a5
	csrrc x7, 323, x15
	li x15, 0xffffffff
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrc x7, 323, x15
	li x15, 0x5a5a5a5a
	bne x15, x7, csr_fail
	li x15, 0x3fc5b750
	csrrc x7, 323, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b00101
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b11010
	li x15, 0x00000005
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b00110
	li x15, 0x0000001a
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b00101
	li x15, 0x00000006
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b11010
	li x15, 0x00000007
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b00110
	li x15, 0x0000001f
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b00101
	li x15, 0x0000001f
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b11010
	li x15, 0x0000001a
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b00010
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrr x7, 323
	li x15, 0x00000000
	bne x15, x7, csr_fail

	j user_mode_code_start
	
	j csr_fail
user_mode_code_start:


	csrw stvec, 0
	csrw sepc, 0

        la x31, user_mode_code
 	csrw sepc, x31
	csrr x28, 0x100
       
	li x29, 0b0
	slli x29, x29, 8
        addi x28, x29, 0
	csrw 0x100, x28
	csrr x29, 0x100
		
	sret

## USER Mode code starts here
user_mode_code:

	# CSR_SIE
	li x5, 0xa5a5a5a5
	csrrw x4, 260, x5
	li x5, 0x00000000
	bne x5, x4, csr_fail
	nop
	nop
	li x5, 0x5a5a5a5a
	csrrw x4, 260, x5
	li x5, 0x00000020
	bne x5, x4, csr_fail
	nop
	li x5, 0xe4ca5ed3
	csrrw x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	nop
	li x5, 0xa5a5a5a5
	csrrs x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	nop
	li x5, 0x5a5a5a5a
	csrrs x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	nop
	li x5, 0x66c2984c
	csrrs x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	nop
	nop
	li x5, 0xa5a5a5a5
	csrrc x4, 260, x5
	li x5, 0x00000222
	bne x5, x4, csr_fail
	nop
	li x5, 0x5a5a5a5a
	csrrc x4, 260, x5
	li x5, 0x00000202
	bne x5, x4, csr_fail
	nop
	nop
	li x5, 0x9d619640
	csrrc x4, 260, x5
	li x5, 0x00000000
	bne x5, x4, csr_fail
	nop
	nop
	csrrwi x4, 260, 0b00101
	li x5, 0x00000000
	bne x5, x4, csr_fail
	nop
	nop
	csrrwi x4, 260, 0b11010
	li x5, 0x00000000
	bne x5, x4, csr_fail
	nop
	nop
	csrrwi x4, 260, 0b00110
	li x5, 0x00000002
	bne x5, x4, csr_fail
	nop
	nop
	csrrsi x4, 260, 0b00101
	li x5, 0x00000002
	bne x5, x4, csr_fail
	nop
	nop
	csrrsi x4, 260, 0b11010
	li x5, 0x00000002
	bne x5, x4, csr_fail
	nop
	nop
	csrrsi x4, 260, 0b01100
	li x5, 0x00000002
	bne x5, x4, csr_fail
	nop
	nop
	csrrci x4, 260, 0b00101
	li x5, 0x00000002
	bne x5, x4, csr_fail
	nop
	nop
	csrrci x4, 260, 0b11010
	li x5, 0x00000002
	bne x5, x4, csr_fail
	nop
	nop
	csrrci x4, 260, 0b10001
	li x5, 0x00000000
	bne x5, x4, csr_fail
	nop
	nop
	csrr x4, 260
	li x5, 0x00000000
	bne x5, x4, csr_fail
	nop


  	# CSR_STVEC
	li x7, 0xa5a5a5a5
	csrrw x1, 261, x7
	li x7, 0x00000000
	bne x7, x1, csr_fail
	nop
	nop
	li x7, 0x5a5a5a5a
	csrrw x1, 261, x7
	li x7, 0xa5a5a5a5
	bne x7, x1, csr_fail
	nop
	li x7, 0xd2ec680e
	csrrw x1, 261, x7
	li x7, 0x5a5a5a58
	bne x7, x1, csr_fail
	nop
	li x7, 0xa5a5a5a5
	csrrs x1, 261, x7
	li x7, 0xd2ec680c
	bne x7, x1, csr_fail
	nop
	li x7, 0x5a5a5a5a
	csrrs x1, 261, x7
	li x7, 0xf7ededad
	bne x7, x1, csr_fail
	nop
	li x7, 0x14191a03
	csrrs x1, 261, x7
	li x7, 0xfffffffd
	bne x7, x1, csr_fail
	nop
	nop
	li x7, 0xa5a5a5a5
	csrrc x1, 261, x7
	li x7, 0xfffffffd
	bne x7, x1, csr_fail
	nop
	li x7, 0x5a5a5a5a
	csrrc x1, 261, x7
	li x7, 0x5a5a5a58
	bne x7, x1, csr_fail
	nop
	nop
	li x7, 0x9f73bde0
	csrrc x1, 261, x7
	li x7, 0x00000000
	bne x7, x1, csr_fail
	nop
	nop
	csrrwi x1, 261, 0b00101
	li x7, 0x00000000
	bne x7, x1, csr_fail
	nop
	nop
	csrrwi x1, 261, 0b11010
	li x7, 0x00000005
	bne x7, x1, csr_fail
	nop
	nop
	csrrwi x1, 261, 0b01011
	li x7, 0x00000018
	bne x7, x1, csr_fail
	nop
	nop
	csrrsi x1, 261, 0b00101
	li x7, 0x00000009
	bne x7, x1, csr_fail
	nop
	nop
	csrrsi x1, 261, 0b11010
	li x7, 0x0000000d
	bne x7, x1, csr_fail
	nop
	nop
	csrrsi x1, 261, 0b00111
	li x7, 0x0000001d
	bne x7, x1, csr_fail
	nop
	nop
	csrrci x1, 261, 0b00101
	li x7, 0x0000001d
	bne x7, x1, csr_fail
	nop
	nop
	csrrci x1, 261, 0b11010
	li x7, 0x00000018
	bne x7, x1, csr_fail
	nop
	nop
	csrrci x1, 261, 0b11010
	li x7, 0x00000000
	bne x7, x1, csr_fail
	nop
	nop
	csrr x1, 261
	li x7, 0x00000000
	bne x7, x1, csr_fail
	nop

	# CSR_SSCRATCH
	li x1, 0xa5a5a5a5
	csrrw x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	nop
	nop
	li x1, 0x5a5a5a5a
	csrrw x3, 320, x1
	li x1, 0xa5a5a5a5
	bne x1, x3, csr_fail
	nop
	li x1, 0xf149b7e8
	csrrw x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	nop
	li x1, 0xa5a5a5a5
	csrrs x3, 320, x1
	li x1, 0xf149b7e8
	bne x1, x3, csr_fail
	nop
	li x1, 0x5a5a5a5a
	csrrs x3, 320, x1
	li x1, 0xf5edb7ed
	bne x1, x3, csr_fail
	nop
	li x1, 0xbcc8c1c2
	csrrs x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	nop
	nop
	li x1, 0xa5a5a5a5
	csrrc x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	nop
	li x1, 0x5a5a5a5a
	csrrc x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	nop
	nop
	li x1, 0x18fd947a
	csrrc x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	nop
	nop
	csrrwi x3, 320, 0b00101
	li x1, 0x00000000
	bne x1, x3, csr_fail
	nop
	nop
	csrrwi x3, 320, 0b11010
	li x1, 0x00000005
	bne x1, x3, csr_fail
	nop
	nop
	csrrwi x3, 320, 0b01010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	nop
	nop
	csrrsi x3, 320, 0b00101
	li x1, 0x0000000a
	bne x1, x3, csr_fail
	nop
	nop
	csrrsi x3, 320, 0b11010
	li x1, 0x0000000f
	bne x1, x3, csr_fail
	nop
	nop
	csrrsi x3, 320, 0b10100
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	nop
	nop
	csrrci x3, 320, 0b00101
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	nop
	nop
	csrrci x3, 320, 0b11010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	nop
	nop
	csrrci x3, 320, 0b00001
	li x1, 0x00000000
	bne x1, x3, csr_fail
	nop
	csrr x3, 320
	li x1, 0x00000000
	bne x1, x3, csr_fail
	nop
	nop

	# CSR_SEPC
	li x12, 0xa5a5a5a5
	csrrw x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	nop
	nop
	li x12, 0x5a5a5a5a
	csrrw x6, 321, x12
	li x12, 0xa5a5a5a4
	bne x12, x6, csr_fail
	nop
	li x12, 0x7a6c28e1
	csrrw x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	nop
	li x12, 0xa5a5a5a5
	csrrs x6, 321, x12
	li x12, 0x7a6c28e0
	bne x12, x6, csr_fail
	nop
	li x12, 0x5a5a5a5a
	csrrs x6, 321, x12
	li x12, 0xffedade4
	bne x12, x6, csr_fail
	nop
	li x12, 0x1228d835
	csrrs x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	nop
	nop
	li x12, 0xa5a5a5a5
	csrrc x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	nop
	li x12, 0x5a5a5a5a
	csrrc x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	nop
	li x12, 0x712201a4
	csrrc x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	nop
	nop
	csrrwi x6, 321, 0b00101
	li x12, 0x00000000
	bne x12, x6, csr_fail
	nop
	nop
	csrrwi x6, 321, 0b11010
	li x12, 0x00000004
	bne x12, x6, csr_fail
	nop
	nop
	csrrwi x6, 321, 0b00010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	nop
	nop
	csrrsi x6, 321, 0b00101
	li x12, 0x00000002
	bne x12, x6, csr_fail
	nop
	nop
	csrrsi x6, 321, 0b11010
	li x12, 0x00000006
	bne x12, x6, csr_fail
	nop
	nop
	csrrsi x6, 321, 0b01001
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	nop
	nop
	csrrci x6, 321, 0b00101
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	nop
	nop
	csrrci x6, 321, 0b11010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	nop
	nop
	csrrci x6, 321, 0b11110
	li x12, 0x00000000
	bne x12, x6, csr_fail
	nop
	nop
	csrr x6, 321
	li x12, 0x00000000
	bne x12, x6, csr_fail
	nop
	nop


	# CSR_SCAUSE
	li x4, 0xa5a5a5a5
	csrrw x7, 322, x4
	li x4, 0x00000000
	bne x4, x7, csr_fail
	nop
	nop
	li x4, 0x5a5a5a5a
	csrrw x7, 322, x4
	li x4, 0xa5a5a5a5
	bne x4, x7, csr_fail
	nop
	li x4, 0x8b85f3c8
	csrrw x7, 322, x4
	li x4, 0x5a5a5a5a
	bne x4, x7, csr_fail
	nop
	li x4, 0xa5a5a5a5
	csrrs x7, 322, x4
	li x4, 0x8b85f3c8
	bne x4, x7, csr_fail
	nop
	li x4, 0x5a5a5a5a
	csrrs x7, 322, x4
	li x4, 0xafa5f7ed
	bne x4, x7, csr_fail
	nop
	li x4, 0x20fff1ae
	csrrs x7, 322, x4
	li x4, 0xffffffff
	bne x4, x7, csr_fail
	nop
	nop
	li x4, 0xa5a5a5a5
	csrrc x7, 322, x4
	li x4, 0xffffffff
	bne x4, x7, csr_fail
	nop
	li x4, 0x5a5a5a5a
	csrrc x7, 322, x4
	li x4, 0x5a5a5a5a
	bne x4, x7, csr_fail
	nop
	nop
	li x4, 0x1ee47ee4
	csrrc x7, 322, x4
	li x4, 0x00000000
	bne x4, x7, csr_fail
	nop
	nop
	csrrwi x7, 322, 0b00101
	li x4, 0x00000000
	bne x4, x7, csr_fail
	nop
	nop
	csrrwi x7, 322, 0b11010
	li x4, 0x00000005
	bne x4, x7, csr_fail
	nop
	nop
	csrrwi x7, 322, 0b11111
	li x4, 0x0000001a
	bne x4, x7, csr_fail
	nop
	nop
	csrrsi x7, 322, 0b00101
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	nop
	nop
	csrrsi x7, 322, 0b11010
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	nop
	nop
	csrrsi x7, 322, 0b00111
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	nop
	nop
	csrrci x7, 322, 0b00101
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	nop
	nop
	csrrci x7, 322, 0b11010
	li x4, 0x0000001a
	bne x4, x7, csr_fail
	nop
	nop
	csrrci x7, 322, 0b10110
	li x4, 0x00000000
	bne x4, x7, csr_fail
	nop
	nop
	csrr x7, 322
	li x4, 0x00000000
	bne x4, x7, csr_fail
	nop
	nop

	# CSR_STVAL
	li x15, 0xa5a5a5a5
	csrrw x7, 323, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	nop
	nop
	li x15, 0x5a5a5a5a
	csrrw x7, 323, x15
	li x15, 0xa5a5a5a5
	bne x15, x7, csr_fail
	nop
	li x15, 0x195a0d46
	csrrw x7, 323, x15
	li x15, 0x5a5a5a5a
	bne x15, x7, csr_fail
	nop
	li x15, 0xa5a5a5a5
	csrrs x7, 323, x15
	li x15, 0x195a0d46
	bne x15, x7, csr_fail
	nop
	li x15, 0x5a5a5a5a
	csrrs x7, 323, x15
	li x15, 0xbdffade7
	bne x15, x7, csr_fail
	nop
	li x15, 0xe82c2396
	csrrs x7, 323, x15
	li x15, 0xffffffff
	bne x15, x7, csr_fail
	nop
	nop
	li x15, 0xa5a5a5a5
	csrrc x7, 323, x15
	li x15, 0xffffffff
	bne x15, x7, csr_fail
	nop
	li x15, 0x5a5a5a5a
	csrrc x7, 323, x15
	li x15, 0x5a5a5a5a
	bne x15, x7, csr_fail
	nop
	nop
	li x15, 0x3fc5b750
	csrrc x7, 323, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	nop
	nop
	csrrwi x7, 323, 0b00101
	li x15, 0x00000000
	bne x15, x7, csr_fail
	nop
	nop
	csrrwi x7, 323, 0b11010
	li x15, 0x00000005
	bne x15, x7, csr_fail
	nop
	nop
	csrrwi x7, 323, 0b00110
	li x15, 0x0000001a
	bne x15, x7, csr_fail
	nop
	nop
	csrrsi x7, 323, 0b00101
	li x15, 0x00000006
	bne x15, x7, csr_fail
	nop
	nop
	csrrsi x7, 323, 0b11010
	li x15, 0x00000007
	bne x15, x7, csr_fail
	nop
	nop
	csrrsi x7, 323, 0b00110
	li x15, 0x0000001f
	bne x15, x7, csr_fail
	nop
	nop
	csrrci x7, 323, 0b00101
	li x15, 0x0000001f
	bne x15, x7, csr_fail
	nop
	nop
	csrrci x7, 323, 0b11010
	li x15, 0x0000001a
	bne x15, x7, csr_fail
	nop
	nop
	csrrci x7, 323, 0b00010
	li x15, 0x00000000
	bne x15, x7, csr_fail
	nop
	nop
	csrr x7, 323
	li x15, 0x00000000
	bne x15, x7, csr_fail
	nop
	nop
	

	j csr_pass

exception_handler:
	csrr x3, 0x300
	srli x3, x3, 11
	andi x3, x3, 0b11
	li x8, 3
	li x9, 1
	beqz x3, user_exception_handler 
	beq x3, x8, machine_exception_handler
	beq x3, x9, supervisor_exception_handler
machine_exception_handler:

	csrr x6, 0x300
        csrr x30, 0x341	    ## Reading MEPC CSR which holds exception origin Address	
        csrr x31, 0x342     ## Reading MCAUSE CSR which holds the cause of exception
        li x2 ,2
        beq x31, x2, next_instr   ## Checking is exception is expected exception or not
        j csr_fail

next_instr:
	csrw 0x342, 0		## Reseting MCAUSE value to 0 before handling new exception
	beq x30, x0, csr_fail
	addi x7, x30, 12
        jr x7			## Jump to MEPC + 12 Address location
	j csr_fail
supervisor_exception_handler:
	csrr x30, 0x341	    ## Reading MEPC CSR which holds exception origin Address		
        csrr x31, 0x342     ## Reading MCAUSE CSR which holds the cause of exception

        li x2 ,2
        beq x31, x2, next_instr1   ## Checking is exception is expected exception or not
        j csr_fail

next_instr1:
	csrw 0x342, 0		## Reseting MCAUSE value to 0 before handling new exception
	beq x30, x0, csr_fail
	#Return to supervisor mode after handling the exception
	csrr x1, 0x300	
	addi x7, x30, 16
	csrw 0x341, x7 
	mret

user_exception_handler:
 	csrr x3, 0x100
 	csrr x30, 0x341	    ## Reading MEPC CSR which holds exception origin Address		
         csrr x31, 0x342     ## Reading MCAUSE CSR which holds the cause of exception
 
         li x2 ,2
         beq x31, x2, next_instr2   ## Checking is exception is expected exception or not
         j csr_fail
 
next_instr2:
 	beq x30, x0, csr_fail
 	#Return to user mode after handling the exception
 	
 	csrr x1, 0x100	
        addi x7, x30, 16
	csrw 0x341, x7
	csrr x8, 0x341
	csrw 0x141, x8
	sret

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
