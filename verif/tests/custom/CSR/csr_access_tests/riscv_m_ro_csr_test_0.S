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

	# CSR_MIMPID
	li x5, 0xa5a5a5a5
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x067ec813
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x52f12149
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xd8bf28b7
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b11000
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b10100
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b10111
	li x5, 0x00000000
	bne x5, x1, csr_fail
  	csrr x1, 3859
  	li x5, 0x00000000
  	bne x5, x1, csr_fail


	# CSR_MHARTID
	csrr x6, 3860
	li x7, 0x00000000
	bne x6, x7, csr_fail
	li x13, 0xa5a5a5a5
	csrrw x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x5a706c83
	csrrw x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x3a3e1cdf
	csrrs x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x407aaf2b
	csrrc x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrwi x10, 3860, 0b00101
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrwi x10, 3860, 0b11010
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrwi x10, 3860, 0b11101
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrsi x10, 3860, 0b00101
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrsi x10, 3860, 0b11010
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrsi x10, 3860, 0b10100
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrci x10, 3860, 0b00101
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrci x10, 3860, 0b11010
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrci x10, 3860, 0b11111
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrr x10, 3860
	li x13, 0x00000000
	bne x13, x10, csr_fail
	
	j supervisor_mode_code_start
	j csr_fail

supervisor_mode_code_start:
	csrw  0x341, 0    ## Writing zero into MEPC CSR
	csrw  0x342, 0    ## Reading Zero into MCAUSE CSR
        
	la x28, user_mode_code_start
	csrw 0x341, x28	

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

	# CSR_MIMPID
	li x5, 0xa5a5a5a5
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x067ec813
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x52f12149
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xd8bf28b7
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b11000
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b10100
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b10111
	li x5, 0x00000000
	bne x5, x1, csr_fail
  	csrr x1, 3859
  	li x5, 0x00000000
  	bne x5, x1, csr_fail

	# CSR_MHARTID
	csrr x6, 3860
	li x7, 0x00000000
	bne x6, x7, csr_fail
	li x13, 0xa5a5a5a5
	csrrw x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x5a706c83
	csrrw x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x3a3e1cdf
	csrrs x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	li x13, 0x407aaf2b
	csrrc x10, 3860, x13
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrwi x10, 3860, 0b00101
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrwi x10, 3860, 0b11010
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrwi x10, 3860, 0b11101
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrsi x10, 3860, 0b00101
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrsi x10, 3860, 0b11010
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrsi x10, 3860, 0b10100
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrci x10, 3860, 0b00101
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrci x10, 3860, 0b11010
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrrci x10, 3860, 0b11111
	li x13, 0x00000000
	bne x13, x10, csr_fail
	csrr x10, 3860
	li x13, 0x00000000
	bne x13, x10, csr_fail
	
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

	# CSR_MIMPID
	li x5, 0xa5a5a5a5
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x067ec813
	csrrw x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x52f12149
	csrrs x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xd8bf28b7
	csrrc x1, 3859, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3859, 0b11000
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3859, 0b10100
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3859, 0b10111
	li x5, 0x00000000
	bne x5, x1, csr_fail
  	csrr x1, 3859
  	li x5, 0x00000000
  	bne x5, x1, csr_fail
	
  	# CSR_MHARTID
	li x5, 0xa5a5a5a5
	csrrw x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x067ec813
	csrrw x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x52f12149
	csrrs x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xd8bf28b7
	csrrc x1, 3860, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3860, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3860, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 3860, 0b11000
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3860, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3860, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 3860, 0b10100
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3860, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3860, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 3860, 0b10111
	li x5, 0x00000000
	bne x5, x1, csr_fail
  	csrr x1, 3860
  	li x5, 0x00000000
  	bne x5, x1, csr_fail
	
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
	addi x7, x30, 12
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
        addi x7, x30, 12
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
