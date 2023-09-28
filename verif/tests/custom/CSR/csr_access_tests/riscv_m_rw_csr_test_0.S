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


##  	# CSR_MIE
  	
##   	li x4, 0xa5a5a5a5
##    	csrrw x12, 772, x4
##    	li x4, 0x00000000
##    	bne x4, x12, csr_fail
##    	li x4, 0x5a5a5a5a
##    	csrrw x12, 772, x4
##    	li x4, 0x000000a0
##    	bne x4, x12, csr_fail
##    	li x4, 0x8280ee3e
##    	csrrw x12, 772, x4
##    	li x4, 0x00000a0a
##    	bne x4, x12, csr_fail
##    	li x4, 0xa5a5a5a5
##    	csrrs x12, 772, x4
##    	li x4, 0x00000a2a
##    	bne x4, x12, csr_fail
##    	li x4, 0x5a5a5a5a
##    	csrrs x12, 772, x4
##    	li x4, 0x00000aaa
##    	bne x4, x12, csr_fail
##    	li x4, 0x270c6b87
##    	csrrs x12, 772, x4
##    	li x4, 0x00000aaa
##    	bne x4, x12, csr_fail
##    	li x4, 0xa5a5a5a5
##    	csrrc x12, 772, x4
##    	li x4, 0x00000aaa
##    	bne x4, x12, csr_fail
##    	li x4, 0x5a5a5a5a
##    	csrrc x12, 772, x4
##    	li x4, 0x00000a0a
##    	bne x4, x12, csr_fail
##    	li x4, 0x2f738936
##    	csrrc x12, 772, x4
##    	li x4, 0x00000000
##    	bne x4, x12, csr_fail
##    	csrrwi x12, 772, 0b00101
##    	li x4, 0x00000000
##    	bne x4, x12, csr_fail
##    	csrrwi x12, 772, 0b11010
##    	li x4, 0x00000000
##    	bne x4, x12, csr_fail
##    	csrrwi x12, 772, 0b11000
##    	li x4, 0x0000000a
##    	bne x4, x12, csr_fail
##    	csrrsi x12, 772, 0b00101
##    	li x4, 0x00000008
##    	bne x4, x12, csr_fail
##    	csrrsi x12, 772, 0b11010
##    	li x4, 0x00000008
##    	bne x4, x12, csr_fail
##    	csrrsi x12, 772, 0b00100
##    	li x4, 0x0000000a
##    	bne x4, x12, csr_fail
##    	csrrci x12, 772, 0b00101
##    	li x4, 0x0000000a
##    	bne x4, x12, csr_fail
##    	csrrci x12, 772, 0b11010
##    	li x4, 0x0000000a
##    	bne x4, x12, csr_fail
##    	csrrci x12, 772, 0b01010
##    	li x4, 0x00000000
##    	bne x4, x12, csr_fail
##    	csrr x12, 772
##    	li x4, 0x00000000
##    	bne x4, x12, csr_fail

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
	
	# CSR_MEPC
	li x9, 0xa5a5a5a5
	csrrw x2, 833, x9
	li x9, 0x00000000
	bne x9, x2, csr_fail
	li x9, 0x5a5a5a5a
	csrrw x2, 833, x9
	li x9, 0xa5a5a5a4
	bne x9, x2, csr_fail
	li x9, 0xc782f024
	csrrw x2, 833, x9
	li x9, 0x5a5a5a5a
	bne x9, x2, csr_fail
	li x9, 0xa5a5a5a5
	csrrs x2, 833, x9
	li x9, 0xc782f024
	bne x9, x2, csr_fail
	li x9, 0x5a5a5a5a
	csrrs x2, 833, x9
	li x9, 0xe7a7f5a4
	bne x9, x2, csr_fail
	li x9, 0x81d6d9bb
	csrrs x2, 833, x9
	li x9, 0xfffffffe
	bne x9, x2, csr_fail
	li x9, 0xa5a5a5a5
	csrrc x2, 833, x9
	li x9, 0xfffffffe
	bne x9, x2, csr_fail
	li x9, 0x5a5a5a5a
	csrrc x2, 833, x9
	li x9, 0x5a5a5a5a
	bne x9, x2, csr_fail
	li x9, 0x52216f2e
	csrrc x2, 833, x9
	li x9, 0x00000000
	bne x9, x2, csr_fail
	csrrwi x2, 833, 0b00101
	li x9, 0x00000000
	bne x9, x2, csr_fail
	csrrwi x2, 833, 0b11010
	li x9, 0x00000004
	bne x9, x2, csr_fail
	csrrwi x2, 833, 0b11100
	li x9, 0x0000001a
	bne x9, x2, csr_fail
	csrrsi x2, 833, 0b00101
	li x9, 0x0000001c
	bne x9, x2, csr_fail
	csrrsi x2, 833, 0b11010
	li x9, 0x0000001c
	bne x9, x2, csr_fail
	csrrsi x2, 833, 0b11110
	li x9, 0x0000001e
	bne x9, x2, csr_fail
	csrrci x2, 833, 0b00101
	li x9, 0x0000001e
	bne x9, x2, csr_fail
	csrrci x2, 833, 0b11010
	li x9, 0x0000001a
	bne x9, x2, csr_fail
	csrrci x2, 833, 0b00111
	li x9, 0x00000000
	bne x9, x2, csr_fail
	csrr x2, 833
	li x9, 0x00000000
	bne x9, x2, csr_fail

	# CSR_MCAUSE
	li x3, 0xa5a5a5a5
	csrrw x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x14, 834, x3
	li x3, 0xa5a5a5a5
	bne x3, x14, csr_fail
	li x3, 0x77b01936
	csrrw x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x14, 834, x3
	li x3, 0x77b01936
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x14, 834, x3
	li x3, 0xf7b5bdb7
	bne x3, x14, csr_fail
	li x3, 0xd2e9bfc7
	csrrs x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	li x3, 0xdf872ab5
	csrrc x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b00101
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b11010
	li x3, 0x00000005
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b01101
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b00101
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b11010
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b10100
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b00101
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b11010
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b00110
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrr x14, 834
	li x3, 0x00000000
	bne x3, x14, csr_fail

	# CSR_MTVAL
	li x1, 0xa5a5a5a5
	csrrw x5, 835, x1
	li x1, 0x00000000
	bne x1, x5, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x5, 835, x1
	li x1, 0xa5a5a5a5
	bne x1, x5, csr_fail
	li x1, 0x69c7015b
	csrrw x5, 835, x1
	li x1, 0x5a5a5a5a
	bne x1, x5, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x5, 835, x1
	li x1, 0x69c7015b
	bne x1, x5, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x5, 835, x1
	li x1, 0xede7a5ff
	bne x1, x5, csr_fail
	li x1, 0xbcf5a4ed
	csrrs x5, 835, x1
	li x1, 0xffffffff
	bne x1, x5, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x5, 835, x1
	li x1, 0xffffffff
	bne x1, x5, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x5, 835, x1
	li x1, 0x5a5a5a5a
	bne x1, x5, csr_fail
	li x1, 0x04e00ec7
	csrrc x5, 835, x1
	li x1, 0x00000000
	bne x1, x5, csr_fail
	csrrwi x5, 835, 0b00101
	li x1, 0x00000000
	bne x1, x5, csr_fail
	csrrwi x5, 835, 0b11010
	li x1, 0x00000005
	bne x1, x5, csr_fail
	csrrwi x5, 835, 0b11000
	li x1, 0x0000001a
	bne x1, x5, csr_fail
	csrrsi x5, 835, 0b00101
	li x1, 0x00000018
	bne x1, x5, csr_fail
	csrrsi x5, 835, 0b11010
	li x1, 0x0000001d
	bne x1, x5, csr_fail
	csrrsi x5, 835, 0b10000
	li x1, 0x0000001f
	bne x1, x5, csr_fail
	csrrci x5, 835, 0b00101
	li x1, 0x0000001f
	bne x1, x5, csr_fail
	csrrci x5, 835, 0b11010
	li x1, 0x0000001a
	bne x1, x5, csr_fail
	csrrci x5, 835, 0b00110
	li x1, 0x00000000
	bne x1, x5, csr_fail
	csrr x5, 835
	li x1, 0x00000000
	bne x1, x5, csr_fail

## 	# CSR_MCOUNTEREN
##  	li x14, 0xa5a5a5a5
##  	csrrw x3, 774, x14
##  	li x14, 0x00000000
##  	bne x14, x3, csr_fail
##  	li x14, 0x5a5a5a5a
##  	csrrw x3, 774, x14
##  	li x14, 0xa5a5a5a5
##  	bne x14, x3, csr_fail
##  	li x14, 0xf1811b91
##  	csrrw x3, 774, x14
##  	li x14, 0x5a5a5a5a
##  	bne x14, x3, csr_fail
##  	li x14, 0xa5a5a5a5
##  	csrrs x3, 774, x14
##  	li x14, 0xf1811b91
##  	bne x14, x3, csr_fail
##  	li x14, 0x5a5a5a5a
##  	csrrs x3, 774, x14
##  	li x14, 0xf5a5bfb5
##  	bne x14, x3, csr_fail
##  	li x14, 0x33487fde
##  	csrrs x3, 774, x14
##  	li x14, 0xffffffff
##  	bne x14, x3, csr_fail
##  	li x14, 0xa5a5a5a5
##  	csrrc x3, 774, x14
##  	li x14, 0xffffffff
##  	bne x14, x3, csr_fail
##  	li x14, 0x5a5a5a5a
##  	csrrc x3, 774, x14
##  	li x14, 0x5a5a5a5a
##  	bne x14, x3, csr_fail
##  	li x14, 0xff06b67c
##  	csrrc x3, 774, x14
##  	li x14, 0x00000000
##  	bne x14, x3, csr_fail
##  	csrrwi x3, 774, 0b00101
##  	li x14, 0x00000000
##  	bne x14, x3, csr_fail
##  	csrrwi x3, 774, 0b11010
##  	li x14, 0x00000005
##  	bne x14, x3, csr_fail
##  	csrrwi x3, 774, 0b00010
##  	li x14, 0x0000001a
##  	bne x14, x3, csr_fail
##  	csrrsi x3, 774, 0b00101
##  	li x14, 0x00000002
##  	bne x14, x3, csr_fail
##  	csrrsi x3, 774, 0b11010
##  	li x14, 0x00000007
##  	bne x14, x3, csr_fail
##  	csrrsi x3, 774, 0b00011
##  	li x14, 0x0000001f
##  	bne x14, x3, csr_fail
##  	csrrci x3, 774, 0b00101
##  	li x14, 0x0000001f
##  	bne x14, x3, csr_fail
##  	csrrci x3, 774, 0b11010
##  	li x14, 0x0000001a
##  	bne x14, x3, csr_fail
##  	csrrci x3, 774, 0b00101
##  	li x14, 0x00000000
##  	bne x14, x3, csr_fail
##  	csrr x3, 774
##  	li x14, 0x00000000
##  	bne x14, x3, csr_fail


 	# CSR_MIDELEG  	
##   	li x6, 0xa5a5a5a5
##   	csrrw x7, 771, x6
##   	li x6, 0x00000000
##   	bne x6, x7, csr_fail
##   	li x6, 0x5a5a5a5a
##   	csrrw x7, 771, x6
##   	li x6, 0x00000020
##   	bne x6, x7, csr_fail
##   	li x6, 0xe532cd4c
##   	csrrw x7, 771, x6
##   	li x6, 0x00000202
##   	bne x6, x7, csr_fail
##   	li x6, 0xa5a5a5a5
##   	csrrs x7, 771, x6
##   	li x6, 0x00000000
##   	bne x6, x7, csr_fail
##   	li x6, 0x5a5a5a5a
##   	csrrs x7, 771, x6
##   	li x6, 0x00000020
##   	bne x6, x7, csr_fail
##   	li x6, 0x1c4c29cb
##   	csrrs x7, 771, x6
##   	li x6, 0x00000222
##   	bne x6, x7, csr_fail
##   	li x6, 0xa5a5a5a5
##   	csrrc x7, 771, x6
##   	li x6, 0x00000222
##   	bne x6, x7, csr_fail
##   	li x6, 0x5a5a5a5a
##   	csrrc x7, 771, x6
##   	li x6, 0x00000202
##   	bne x6, x7, csr_fail
##   	li x6, 0x407ecd51
##   	csrrc x7, 771, x6
##   	li x6, 0x00000000
##   	bne x6, x7, csr_fail
##   	csrrwi x7, 771, 0b00101
##   	li x6, 0x00000000
##   	bne x6, x7, csr_fail
##   	csrrwi x7, 771, 0b11010
##   	li x6, 0x00000000
##   	bne x6, x7, csr_fail
##   	csrrwi x7, 771, 0b11011
##   	li x6, 0x00000002
##   	bne x6, x7, csr_fail
##   	csrrsi x7, 771, 0b00101
##   	li x6, 0x00000002
##   	bne x6, x7, csr_fail
##   	csrrsi x7, 771, 0b11010
##   	li x6, 0x00000002
##   	bne x6, x7, csr_fail
##   	csrrsi x7, 771, 0b11100
##   	li x6, 0x00000002
##   	bne x6, x7, csr_fail
##   	csrrci x7, 771, 0b00101
##   	li x6, 0x00000002
##   	bne x6, x7, csr_fail
##   	csrrci x7, 771, 0b11010
##   	li x6, 0x00000002
##   	bne x6, x7, csr_fail
##   	csrrci x7, 771, 0b10011
##   	li x6, 0x00000000
##   	bne x6, x7, csr_fail
##   	csrr x7, 771
##   	li x6, 0x00000000
##   	bne x6, x7, csr_fail

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

	# CSR_MIE
	li x4, 0xa5a5a5a5
	csrrw x12, 772, x4
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	li x4, 0x5a5a5a5a
	csrrw x12, 772, x4
	li x4, 0x000000a0
	bne x4, x12, csr_fail
	nop
	li x4, 0x8280ee3e
	csrrw x12, 772, x4
	li x4, 0x00000a0a
	bne x4, x12, csr_fail
	nop
	li x4, 0xa5a5a5a5
	csrrs x12, 772, x4
	li x4, 0x00000a2a
	bne x4, x12, csr_fail
	nop
	li x4, 0x5a5a5a5a
	csrrs x12, 772, x4
	li x4, 0x00000aaa
	bne x4, x12, csr_fail
	nop
	li x4, 0x270c6b87
	csrrs x12, 772, x4
	li x4, 0x00000aaa
	bne x4, x12, csr_fail
	nop
	nop
	li x4, 0xa5a5a5a5
	csrrc x12, 772, x4
	li x4, 0x00000aaa
	bne x4, x12, csr_fail
	nop
	li x4, 0x5a5a5a5a
	csrrc x12, 772, x4
	li x4, 0x00000a0a
	bne x4, x12, csr_fail
	nop
	nop
	li x4, 0x2f738936
	csrrc x12, 772, x4
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	csrrwi x12, 772, 0b00101
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	csrrwi x12, 772, 0b11010
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	csrrwi x12, 772, 0b11000
	li x4, 0x0000000a
	bne x4, x12, csr_fail
	nop
	nop
	csrrsi x12, 772, 0b00101
	li x4, 0x00000008
	bne x4, x12, csr_fail
	nop
	nop
	csrrsi x12, 772, 0b11010
	li x4, 0x00000008
	bne x4, x12, csr_fail
	nop
	nop
	csrrsi x12, 772, 0b00100
	li x4, 0x0000000a
	bne x4, x12, csr_fail
	nop
	nop
	csrrci x12, 772, 0b00101
	li x4, 0x0000000a
	bne x4, x12, csr_fail
	nop
	nop
	csrrci x12, 772, 0b11010
	li x4, 0x0000000a
	bne x4, x12, csr_fail
	nop
	nop
	csrrci x12, 772, 0b01010
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	csrr x12, 772
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop


	# CSR_MSCRATCH
	li x10, 0xa5a5a5a5
	csrrw x14, 0x340, x10
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop
	nop
	li x10, 0x5a5a5a5a
	csrrw x14, 0x340, x10
	li x10, 0xa5a5a5a5
	bne x10, x14, csr_fail
	nop
	li x10, 0x6c218674
	csrrw x14, 0x340, x10
	li x10, 0x5a5a5a5a
	bne x10, x14, csr_fail
	nop
	li x10, 0xa5a5a5a5
	csrrs x14, 0x340, x10
	li x10, 0x6c218674
	bne x10, x14, csr_fail
	nop
	li x10, 0x5a5a5a5a
	csrrs x14, 0x340, x10
	li x10, 0xeda5a7f5
	bne x10, x14, csr_fail
	nop
	li x10, 0xdd2d25a6
	csrrs x14, 0x340, x10
	li x10, 0xffffffff
	bne x10, x14, csr_fail
	nop
	nop
	li x10, 0xa5a5a5a5
	csrrc x14, 0x340, x10
	li x10, 0xffffffff
	bne x10, x14, csr_fail
	nop
	li x10, 0x5a5a5a5a
	csrrc x14, 0x340, x10
	li x10, 0x5a5a5a5a
	bne x10, x14, csr_fail
	nop
	nop
	li x10, 0x8959179c
	csrrc x14, 0x340, x10
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop
	nop
	csrrwi x14, 0x340, 0b00101
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop
	nop
	csrrwi x14, 0x340, 0b11010
	li x10, 0x00000005
	bne x10, x14, csr_fail
	nop
	nop
	csrrwi x14, 0x340, 0b01110
	li x10, 0x0000001a
	bne x10, x14, csr_fail
	nop
	nop
	csrrsi x14, 0x340, 0b00101
	li x10, 0x0000000e
	bne x10, x14, csr_fail
	nop
	nop
	csrrsi x14, 0x340, 0b11010
	li x10, 0x0000000f
	bne x10, x14, csr_fail
	nop
	nop
	csrrsi x14, 0x340, 0b00000
	li x10, 0x0000001f
	bne x10, x14, csr_fail
	nop
	nop
	csrrci x14, 0x340, 0b00101
	li x10, 0x0000001f
	bne x10, x14, csr_fail
	nop
	nop
	csrrci x14, 0x340, 0b11010
	li x10, 0x0000001a
	bne x10, x14, csr_fail
	nop
	nop
	csrrci x14, 0x340, 0b00100
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop
	nop
	csrr x14, 0x340
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop

	# CSR_MEPC
	li x9, 0xa5a5a5a5
	csrrw x2, 833, x9
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	li x9, 0x5a5a5a5a
	csrrw x2, 833, x9
	li x9, 0xa5a5a5a4
	bne x9, x2, csr_fail
	nop
	li x9, 0xc782f024
	csrrw x2, 833, x9
	li x9, 0x5a5a5a5a
	bne x9, x2, csr_fail
	nop
	li x9, 0xa5a5a5a5
	csrrs x2, 833, x9
	li x9, 0xc782f024
	bne x9, x2, csr_fail
	nop
	li x9, 0x5a5a5a5a
	csrrs x2, 833, x9
	li x9, 0xe7a7f5a4
	bne x9, x2, csr_fail
	nop
	li x9, 0x81d6d9bb
	csrrs x2, 833, x9
	li x9, 0xfffffffe
	bne x9, x2, csr_fail
	nop
	nop
	li x9, 0xa5a5a5a5
	csrrc x2, 833, x9
	li x9, 0xfffffffe
	bne x9, x2, csr_fail
	nop
	li x9, 0x5a5a5a5a
	csrrc x2, 833, x9
	li x9, 0x5a5a5a5a
	bne x9, x2, csr_fail
	nop
	li x9, 0x52216f2e
	csrrc x2, 833, x9
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	csrrwi x2, 833, 0b00101
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	csrrwi x2, 833, 0b11010
	li x9, 0x00000004
	bne x9, x2, csr_fail
	nop
	nop
	csrrwi x2, 833, 0b11100
	li x9, 0x0000001a
	bne x9, x2, csr_fail
	nop
	nop
	csrrsi x2, 833, 0b00101
	li x9, 0x0000001c
	bne x9, x2, csr_fail
	nop
	nop
	csrrsi x2, 833, 0b11010
	li x9, 0x0000001c
	bne x9, x2, csr_fail
	nop
	nop
	csrrsi x2, 833, 0b11110
	li x9, 0x0000001e
	bne x9, x2, csr_fail
	nop
	nop
	csrrci x2, 833, 0b00101
	li x9, 0x0000001e
	bne x9, x2, csr_fail
	nop
	nop
	csrrci x2, 833, 0b11010
	li x9, 0x0000001a
	bne x9, x2, csr_fail
	nop
	nop
	csrrci x2, 833, 0b00111
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	csrr x2, 833
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop

	# CSR_MCAUSE
	li x3, 0xa5a5a5a5
	csrrw x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop
	li x3, 0x5a5a5a5a
	csrrw x14, 834, x3
	li x3, 0xa5a5a5a5
	bne x3, x14, csr_fail
	nop
	li x3, 0x77b01936
	csrrw x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	nop
	li x3, 0xa5a5a5a5
	csrrs x14, 834, x3
	li x3, 0x77b01936
	bne x3, x14, csr_fail
	nop
	li x3, 0x5a5a5a5a
	csrrs x14, 834, x3
	li x3, 0xf7b5bdb7
	bne x3, x14, csr_fail
	nop
	li x3, 0xd2e9bfc7
	csrrs x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	nop
	nop
	li x3, 0xa5a5a5a5
	csrrc x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	nop
	li x3, 0x5a5a5a5a
	csrrc x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	nop
	li x3, 0xdf872ab5
	csrrc x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop
	csrrwi x14, 834, 0b00101
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop
	csrrwi x14, 834, 0b11010
	li x3, 0x00000005
	bne x3, x14, csr_fail
	nop
	nop
	csrrwi x14, 834, 0b01101
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	nop
	nop
	csrrsi x14, 834, 0b00101
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	nop
	nop
	csrrsi x14, 834, 0b11010
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	nop
	nop
	csrrsi x14, 834, 0b10100
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	nop
	nop
	csrrci x14, 834, 0b00101
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	nop
	nop
	csrrci x14, 834, 0b11010
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	nop
	nop
	csrrci x14, 834, 0b00110
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop
	csrr x14, 834
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop

	# CSR_MTVAL
	li x1, 0xa5a5a5a5
	csrrw x5, 835, x1
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop
	li x1, 0x5a5a5a5a
	csrrw x5, 835, x1
	li x1, 0xa5a5a5a5
	bne x1, x5, csr_fail
	nop
	li x1, 0x69c7015b
	csrrw x5, 835, x1
	li x1, 0x5a5a5a5a
	bne x1, x5, csr_fail
	nop
	li x1, 0xa5a5a5a5
	csrrs x5, 835, x1
	li x1, 0x69c7015b
	bne x1, x5, csr_fail
	nop
	li x1, 0x5a5a5a5a
	csrrs x5, 835, x1
	li x1, 0xede7a5ff
	bne x1, x5, csr_fail
	nop
	li x1, 0xbcf5a4ed
	csrrs x5, 835, x1
	li x1, 0xffffffff
	bne x1, x5, csr_fail
	nop
	nop
	li x1, 0xa5a5a5a5
	csrrc x5, 835, x1
	li x1, 0xffffffff
	bne x1, x5, csr_fail
	nop
	li x1, 0x5a5a5a5a
	csrrc x5, 835, x1
	li x1, 0x5a5a5a5a
	bne x1, x5, csr_fail
	nop
	li x1, 0x04e00ec7
	csrrc x5, 835, x1
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop
	csrrwi x5, 835, 0b00101
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop
	csrrwi x5, 835, 0b11010
	li x1, 0x00000005
	bne x1, x5, csr_fail
	nop
	nop
	csrrwi x5, 835, 0b11000
	li x1, 0x0000001a
	bne x1, x5, csr_fail
	nop
	nop
	csrrsi x5, 835, 0b00101
	li x1, 0x00000018
	bne x1, x5, csr_fail
	nop
	nop
	csrrsi x5, 835, 0b11010
	li x1, 0x0000001d
	bne x1, x5, csr_fail
	nop
	nop
	csrrsi x5, 835, 0b10000
	li x1, 0x0000001f
	bne x1, x5, csr_fail
	nop
	nop
	csrrci x5, 835, 0b00101
	li x1, 0x0000001f
	bne x1, x5, csr_fail
	nop
	nop
	csrrci x5, 835, 0b11010
	li x1, 0x0000001a
	bne x1, x5, csr_fail
	nop
	nop
	csrrci x5, 835, 0b00110
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop
	csrr x5, 835
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop

	# CSR_MCOUNTEREN
	li x14, 0xa5a5a5a5
	csrrw x3, 774, x14
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop
	li x14, 0x5a5a5a5a
	csrrw x3, 774, x14
	li x14, 0xa5a5a5a5
	bne x14, x3, csr_fail
	nop
	li x14, 0xf1811b91
	csrrw x3, 774, x14
	li x14, 0x5a5a5a5a
	bne x14, x3, csr_fail
	nop
	li x14, 0xa5a5a5a5
	csrrs x3, 774, x14
	li x14, 0xf1811b91
	bne x14, x3, csr_fail
	nop
	li x14, 0x5a5a5a5a
	csrrs x3, 774, x14
	li x14, 0xf5a5bfb5
	bne x14, x3, csr_fail
	nop
	li x14, 0x33487fde
	csrrs x3, 774, x14
	li x14, 0xffffffff
	bne x14, x3, csr_fail
	nop
	nop
	li x14, 0xa5a5a5a5
	csrrc x3, 774, x14
	li x14, 0xffffffff
	bne x14, x3, csr_fail
	nop
	li x14, 0x5a5a5a5a
	csrrc x3, 774, x14
	li x14, 0x5a5a5a5a
	bne x14, x3, csr_fail
	nop
	nop
	li x14, 0xff06b67c
	csrrc x3, 774, x14
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop
	csrrwi x3, 774, 0b00101
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop
	csrrwi x3, 774, 0b11010
	li x14, 0x00000005
	bne x14, x3, csr_fail
	nop
	nop
	csrrwi x3, 774, 0b00010
	li x14, 0x0000001a
	bne x14, x3, csr_fail
	nop
	nop
	csrrsi x3, 774, 0b00101
	li x14, 0x00000002
	bne x14, x3, csr_fail
	nop
	nop
	csrrsi x3, 774, 0b11010
	li x14, 0x00000007
	bne x14, x3, csr_fail
	nop
	nop
	csrrsi x3, 774, 0b00011
	li x14, 0x0000001f
	bne x14, x3, csr_fail
	nop
	nop
	csrrci x3, 774, 0b00101
	li x14, 0x0000001f
	bne x14, x3, csr_fail
	nop
	nop
	csrrci x3, 774, 0b11010
	li x14, 0x0000001a
	bne x14, x3, csr_fail
	nop
	nop
	csrrci x3, 774, 0b00101
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop
	csrr x3, 774
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop

	# CSR_MIDELEG
	li x6, 0xa5a5a5a5
	csrrw x7, 771, x6
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	li x6, 0x5a5a5a5a
	csrrw x7, 771, x6
	li x6, 0x00000020
	bne x6, x7, csr_fail
	nop
	li x6, 0xe532cd4c
	csrrw x7, 771, x6
	li x6, 0x00000202
	bne x6, x7, csr_fail
	nop
	li x6, 0xa5a5a5a5
	csrrs x7, 771, x6
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	li x6, 0x5a5a5a5a
	csrrs x7, 771, x6
	li x6, 0x00000020
	bne x6, x7, csr_fail
	nop
	li x6, 0x1c4c29cb
	csrrs x7, 771, x6
	li x6, 0x00000222
	bne x6, x7, csr_fail
	nop
	nop
	li x6, 0xa5a5a5a5
	csrrc x7, 771, x6
	li x6, 0x00000222
	bne x6, x7, csr_fail
	nop
	li x6, 0x5a5a5a5a
	csrrc x7, 771, x6
	li x6, 0x00000202
	bne x6, x7, csr_fail
	nop
	nop
	li x6, 0x407ecd51
	csrrc x7, 771, x6
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	csrrwi x7, 771, 0b00101
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	csrrwi x7, 771, 0b11010
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	csrrwi x7, 771, 0b11011
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrsi x7, 771, 0b00101
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrsi x7, 771, 0b11010
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrsi x7, 771, 0b11100
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrci x7, 771, 0b00101
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrci x7, 771, 0b11010
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrci x7, 771, 0b10011
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	csrr x7, 771
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop

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

	# CSR_MIE
	li x4, 0xa5a5a5a5
	csrrw x12, 772, x4
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	li x4, 0x5a5a5a5a
	csrrw x12, 772, x4
	li x4, 0x000000a0
	bne x4, x12, csr_fail
	nop
	li x4, 0x8280ee3e
	csrrw x12, 772, x4
	li x4, 0x00000a0a
	bne x4, x12, csr_fail
	nop
	li x4, 0xa5a5a5a5
	csrrs x12, 772, x4
	li x4, 0x00000a2a
	bne x4, x12, csr_fail
	nop
	li x4, 0x5a5a5a5a
	csrrs x12, 772, x4
	li x4, 0x00000aaa
	bne x4, x12, csr_fail
	nop
	li x4, 0x270c6b87
	csrrs x12, 772, x4
	li x4, 0x00000aaa
	bne x4, x12, csr_fail
	nop
	nop
	li x4, 0xa5a5a5a5
	csrrc x12, 772, x4
	li x4, 0x00000aaa
	bne x4, x12, csr_fail
	nop
	li x4, 0x5a5a5a5a
	csrrc x12, 772, x4
	li x4, 0x00000a0a
	bne x4, x12, csr_fail
	nop
	nop
	li x4, 0x2f738936
	csrrc x12, 772, x4
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	csrrwi x12, 772, 0b00101
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	csrrwi x12, 772, 0b11010
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	csrrwi x12, 772, 0b11000
	li x4, 0x0000000a
	bne x4, x12, csr_fail
	nop
	nop
	csrrsi x12, 772, 0b00101
	li x4, 0x00000008
	bne x4, x12, csr_fail
	nop
	nop
	csrrsi x12, 772, 0b11010
	li x4, 0x00000008
	bne x4, x12, csr_fail
	nop
	nop
	csrrsi x12, 772, 0b00100
	li x4, 0x0000000a
	bne x4, x12, csr_fail
	nop
	nop
	csrrci x12, 772, 0b00101
	li x4, 0x0000000a
	bne x4, x12, csr_fail
	nop
	nop
	csrrci x12, 772, 0b11010
	li x4, 0x0000000a
	bne x4, x12, csr_fail
	nop
	nop
	csrrci x12, 772, 0b01010
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	csrr x12, 772
	li x4, 0x00000000
	bne x4, x12, csr_fail
	nop
	nop
	
	#CSR_MSCRATCH 
	li x10, 0xa5a5a5a5
	csrrw x14, 0x340, x10
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop
	nop
	li x10, 0x5a5a5a5a
	csrrw x14, 0x340, x10
	li x10, 0xa5a5a5a5
	bne x10, x14, csr_fail
	nop
	li x10, 0x6c218674
	csrrw x14, 0x340, x10
	li x10, 0x5a5a5a5a
	bne x10, x14, csr_fail
	nop
	li x10, 0xa5a5a5a5
	csrrs x14, 0x340, x10
	li x10, 0x6c218674
	bne x10, x14, csr_fail
	nop
	li x10, 0x5a5a5a5a
	csrrs x14, 0x340, x10
	li x10, 0xeda5a7f5
	bne x10, x14, csr_fail
	nop
	li x10, 0xdd2d25a6
	csrrs x14, 0x340, x10
	li x10, 0xffffffff
	bne x10, x14, csr_fail
	nop
	nop
	li x10, 0xa5a5a5a5
	csrrc x14, 0x340, x10
	li x10, 0xffffffff
	bne x10, x14, csr_fail
	nop
	li x10, 0x5a5a5a5a
	csrrc x14, 0x340, x10
	li x10, 0x5a5a5a5a
	bne x10, x14, csr_fail
	nop
	nop
	li x10, 0x8959179c
	csrrc x14, 0x340, x10
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop
	nop
	csrrwi x14, 0x340, 0b00101
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop
	nop
	csrrwi x14, 0x340, 0b11010
	li x10, 0x00000005
	bne x10, x14, csr_fail
	nop
	nop
	csrrwi x14, 0x340, 0b01110
	li x10, 0x0000001a
	bne x10, x14, csr_fail
	nop
	nop
	csrrsi x14, 0x340, 0b00101
	li x10, 0x0000000e
	bne x10, x14, csr_fail
	nop
	nop
	csrrsi x14, 0x340, 0b11010
	li x10, 0x0000000f
	bne x10, x14, csr_fail
	nop
	nop
	csrrsi x14, 0x340, 0b00000
	li x10, 0x0000001f
	bne x10, x14, csr_fail
	nop
	nop
	csrrci x14, 0x340, 0b00101
	li x10, 0x0000001f
	bne x10, x14, csr_fail
	nop
	nop
	csrrci x14, 0x340, 0b11010
	li x10, 0x0000001a
	bne x10, x14, csr_fail
	nop
	nop
	csrrci x14, 0x340, 0b00100
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop
	nop
	csrr x14, 0x340
	li x10, 0x00000000
	bne x10, x14, csr_fail
	nop

	# CSR_MEPC
	li x9, 0xa5a5a5a5
	csrrw x2, 833, x9
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	li x9, 0x5a5a5a5a
	csrrw x2, 833, x9
	li x9, 0xa5a5a5a4
	bne x9, x2, csr_fail
	nop
	li x9, 0xc782f024
	csrrw x2, 833, x9
	li x9, 0x5a5a5a5a
	bne x9, x2, csr_fail
	nop
	li x9, 0xa5a5a5a5
	csrrs x2, 833, x9
	li x9, 0xc782f024
	bne x9, x2, csr_fail
	nop
	li x9, 0x5a5a5a5a
	csrrs x2, 833, x9
	li x9, 0xe7a7f5a4
	bne x9, x2, csr_fail
	nop
	li x9, 0x81d6d9bb
	csrrs x2, 833, x9
	li x9, 0xfffffffe
	bne x9, x2, csr_fail
	nop
	nop
	li x9, 0xa5a5a5a5
	csrrc x2, 833, x9
	li x9, 0xfffffffe
	bne x9, x2, csr_fail
	nop
	li x9, 0x5a5a5a5a
	csrrc x2, 833, x9
	li x9, 0x5a5a5a5a
	bne x9, x2, csr_fail
	nop
	li x9, 0x52216f2e
	csrrc x2, 833, x9
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	csrrwi x2, 833, 0b00101
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	csrrwi x2, 833, 0b11010
	li x9, 0x00000004
	bne x9, x2, csr_fail
	nop
	nop
	csrrwi x2, 833, 0b11100
	li x9, 0x0000001a
	bne x9, x2, csr_fail
	nop
	nop
	csrrsi x2, 833, 0b00101
	li x9, 0x0000001c
	bne x9, x2, csr_fail
	nop
	nop
	csrrsi x2, 833, 0b11010
	li x9, 0x0000001c
	bne x9, x2, csr_fail
	nop
	nop
	csrrsi x2, 833, 0b11110
	li x9, 0x0000001e
	bne x9, x2, csr_fail
	nop
	nop
	csrrci x2, 833, 0b00101
	li x9, 0x0000001e
	bne x9, x2, csr_fail
	nop
	nop
	csrrci x2, 833, 0b11010
	li x9, 0x0000001a
	bne x9, x2, csr_fail
	nop
	nop
	csrrci x2, 833, 0b00111
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	csrr x2, 833
	li x9, 0x00000000
	bne x9, x2, csr_fail
	nop
	nop
	

	# CSR_MCAUSE
	li x3, 0xa5a5a5a5
	csrrw x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop
	li x3, 0x5a5a5a5a
	csrrw x14, 834, x3
	li x3, 0xa5a5a5a5
	bne x3, x14, csr_fail
	nop
	li x3, 0x77b01936
	csrrw x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	nop
	li x3, 0xa5a5a5a5
	csrrs x14, 834, x3
	li x3, 0x77b01936
	bne x3, x14, csr_fail
	nop
	li x3, 0x5a5a5a5a
	csrrs x14, 834, x3
	li x3, 0xf7b5bdb7
	bne x3, x14, csr_fail
	nop
	li x3, 0xd2e9bfc7
	csrrs x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	nop
	nop
	li x3, 0xa5a5a5a5
	csrrc x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	nop
	li x3, 0x5a5a5a5a
	csrrc x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	nop
	li x3, 0xdf872ab5
	csrrc x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop
	csrrwi x14, 834, 0b00101
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop
	csrrwi x14, 834, 0b11010
	li x3, 0x00000005
	bne x3, x14, csr_fail
	nop
	nop
	csrrwi x14, 834, 0b01101
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	nop
	nop
	csrrsi x14, 834, 0b00101
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	nop
	nop
	csrrsi x14, 834, 0b11010
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	nop
	nop
	csrrsi x14, 834, 0b10100
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	nop
	nop
	csrrci x14, 834, 0b00101
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	nop
	nop
	csrrci x14, 834, 0b11010
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	nop
	nop
	csrrci x14, 834, 0b00110
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop
	csrr x14, 834
	li x3, 0x00000000
	bne x3, x14, csr_fail
	nop
	nop

	# CSR_MTVAL
	li x1, 0xa5a5a5a5
	csrrw x5, 835, x1
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop
	li x1, 0x5a5a5a5a
	csrrw x5, 835, x1
	li x1, 0xa5a5a5a5
	bne x1, x5, csr_fail
	nop
	li x1, 0x69c7015b
	csrrw x5, 835, x1
	li x1, 0x5a5a5a5a
	bne x1, x5, csr_fail
	nop
	li x1, 0xa5a5a5a5
	csrrs x5, 835, x1
	li x1, 0x69c7015b
	bne x1, x5, csr_fail
	nop
	li x1, 0x5a5a5a5a
	csrrs x5, 835, x1
	li x1, 0xede7a5ff
	bne x1, x5, csr_fail
	nop
	li x1, 0xbcf5a4ed
	csrrs x5, 835, x1
	li x1, 0xffffffff
	bne x1, x5, csr_fail
	nop
	nop
	li x1, 0xa5a5a5a5
	csrrc x5, 835, x1
	li x1, 0xffffffff
	bne x1, x5, csr_fail
	nop
	li x1, 0x5a5a5a5a
	csrrc x5, 835, x1
	li x1, 0x5a5a5a5a
	bne x1, x5, csr_fail
	nop
	li x1, 0x04e00ec7
	csrrc x5, 835, x1
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop
	csrrwi x5, 835, 0b00101
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop
	csrrwi x5, 835, 0b11010
	li x1, 0x00000005
	bne x1, x5, csr_fail
	nop
	nop
	csrrwi x5, 835, 0b11000
	li x1, 0x0000001a
	bne x1, x5, csr_fail
	nop
	nop
	csrrsi x5, 835, 0b00101
	li x1, 0x00000018
	bne x1, x5, csr_fail
	nop
	nop
	csrrsi x5, 835, 0b11010
	li x1, 0x0000001d
	bne x1, x5, csr_fail
	nop
	nop
	csrrsi x5, 835, 0b10000
	li x1, 0x0000001f
	bne x1, x5, csr_fail
	nop
	nop
	csrrci x5, 835, 0b00101
	li x1, 0x0000001f
	bne x1, x5, csr_fail
	nop
	nop
	csrrci x5, 835, 0b11010
	li x1, 0x0000001a
	bne x1, x5, csr_fail
	nop
	nop
	csrrci x5, 835, 0b00110
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop
	csrr x5, 835
	li x1, 0x00000000
	bne x1, x5, csr_fail
	nop
	nop

	# CSR_MCOUNTEREN
	li x14, 0xa5a5a5a5
	csrrw x3, 774, x14
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop
	li x14, 0x5a5a5a5a
	csrrw x3, 774, x14
	li x14, 0xa5a5a5a5
	bne x14, x3, csr_fail
	nop
	li x14, 0xf1811b91
	csrrw x3, 774, x14
	li x14, 0x5a5a5a5a
	bne x14, x3, csr_fail
	nop
	li x14, 0xa5a5a5a5
	csrrs x3, 774, x14
	li x14, 0xf1811b91
	bne x14, x3, csr_fail
	nop
	li x14, 0x5a5a5a5a
	csrrs x3, 774, x14
	li x14, 0xf5a5bfb5
	bne x14, x3, csr_fail
	nop
	li x14, 0x33487fde
	csrrs x3, 774, x14
	li x14, 0xffffffff
	bne x14, x3, csr_fail
	nop
	nop
	li x14, 0xa5a5a5a5
	csrrc x3, 774, x14
	li x14, 0xffffffff
	bne x14, x3, csr_fail
	nop
	li x14, 0x5a5a5a5a
	csrrc x3, 774, x14
	li x14, 0x5a5a5a5a
	bne x14, x3, csr_fail
	nop
	nop
	li x14, 0xff06b67c
	csrrc x3, 774, x14
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop
	csrrwi x3, 774, 0b00101
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop
	csrrwi x3, 774, 0b11010
	li x14, 0x00000005
	bne x14, x3, csr_fail
	nop
	nop
	csrrwi x3, 774, 0b00010
	li x14, 0x0000001a
	bne x14, x3, csr_fail
	nop
	nop
	csrrsi x3, 774, 0b00101
	li x14, 0x00000002
	bne x14, x3, csr_fail
	nop
	nop
	csrrsi x3, 774, 0b11010
	li x14, 0x00000007
	bne x14, x3, csr_fail
	nop
	nop
	csrrsi x3, 774, 0b00011
	li x14, 0x0000001f
	bne x14, x3, csr_fail
	nop
	nop
	csrrci x3, 774, 0b00101
	li x14, 0x0000001f
	bne x14, x3, csr_fail
	nop
	nop
	csrrci x3, 774, 0b11010
	li x14, 0x0000001a
	bne x14, x3, csr_fail
	nop
	nop
	csrrci x3, 774, 0b00101
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop
	csrr x3, 774
	li x14, 0x00000000
	bne x14, x3, csr_fail
	nop
	nop

	# CSR_MIDELEG
	li x6, 0xa5a5a5a5
	csrrw x7, 771, x6
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	li x6, 0x5a5a5a5a
	csrrw x7, 771, x6
	li x6, 0x00000020
	bne x6, x7, csr_fail
	nop
	li x6, 0xe532cd4c
	csrrw x7, 771, x6
	li x6, 0x00000202
	bne x6, x7, csr_fail
	nop
	li x6, 0xa5a5a5a5
	csrrs x7, 771, x6
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	li x6, 0x5a5a5a5a
	csrrs x7, 771, x6
	li x6, 0x00000020
	bne x6, x7, csr_fail
	nop
	li x6, 0x1c4c29cb
	csrrs x7, 771, x6
	li x6, 0x00000222
	bne x6, x7, csr_fail
	nop
	nop
	li x6, 0xa5a5a5a5
	csrrc x7, 771, x6
	li x6, 0x00000222
	bne x6, x7, csr_fail
	nop
	li x6, 0x5a5a5a5a
	csrrc x7, 771, x6
	li x6, 0x00000202
	bne x6, x7, csr_fail
	nop
	nop
	li x6, 0x407ecd51
	csrrc x7, 771, x6
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	csrrwi x7, 771, 0b00101
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	csrrwi x7, 771, 0b11010
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	csrrwi x7, 771, 0b11011
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrsi x7, 771, 0b00101
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrsi x7, 771, 0b11010
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrsi x7, 771, 0b11100
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrci x7, 771, 0b00101
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrci x7, 771, 0b11010
	li x6, 0x00000002
	bne x6, x7, csr_fail
	nop
	nop
	csrrci x7, 771, 0b10011
	li x6, 0x00000000
	bne x6, x7, csr_fail
	nop
	nop
	csrr x7, 771
	li x6, 0x00000000
	bne x6, x7, csr_fail
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
	addi x7, x30, 20
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
 	#Return to supervisor mode after handling the exception
 	
 	csrr x1, 0x100	
        addi x7, x30, 20
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



