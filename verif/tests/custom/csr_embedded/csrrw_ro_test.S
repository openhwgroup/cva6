# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

.globl main
main:
    #Start CSR tests: Write/Read all registers in a random order including read only ones
    #Handle exceptions
    la x6, exception_handler
    csrw mtvec, x6  ## Load the address of the exception handler into MTVEC
    csrw 0x341, x0  ## Writing Zero to MEPC CSR
    csrw 0x342, x0  ## Writing Zero to MCAUSE CSR
    #End Handle exceptions

    #User ignored registers: MTVEC ,

    ##########################
    #MHPMCOUNTER25 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5ac46a7d} 
    ##########################
    #MHPMCOUNTER25 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write value 0x0
    li x3, 0x0
    csrw 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write value 0x5ac46a7d
    li x3, 0x5ac46a7d
    csrw 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    ##########################
    #MHPMCOUNTERH27 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcce56853} 
    ##########################
    #MHPMCOUNTERH27 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write value 0x0
    li x3, 0x0
    csrw 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write value 0xcce56853
    li x3, 0xcce56853
    csrw 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    ##########################
    #MHPMEVENT29 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfbfbaaa8} 
    ##########################
    #MHPMEVENT29 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write value 0x0
    li x3, 0x0
    csrw 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write value 0xfbfbaaa8
    li x3, 0xfbfbaaa8
    csrw 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    ##########################
    #MHPMEVENT24 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h36180877} 
    ##########################
    #MHPMEVENT24 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write value 0x0
    li x3, 0x0
    csrw 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write value 0x36180877
    li x3, 0x36180877
    csrw 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    ##########################
    #MHPMCOUNTER23 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h71bf4cfe} 
    ##########################
    #MHPMCOUNTER23 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write value 0x0
    li x3, 0x0
    csrw 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write value 0x71bf4cfe
    li x3, 0x71bf4cfe
    csrw 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    ##########################
    #MHPMCOUNTERH12 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h489aa54} 
    ##########################
    #MHPMCOUNTERH12 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write value 0x0
    li x3, 0x0
    csrw 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write value 0x489aa54
    li x3, 0x489aa54
    csrw 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    ##########################
    #PMPCFG2 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h81c87eac} 
    ##########################
    #PMPCFG2 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x0
    li x3, 0x0
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x81c87eac
    li x3, 0x81c87eac
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    ##########################
    #MIE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha3bffb1b} 
    ##########################
    #MIE Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x55555555
    li x3, 0x55555555
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0xa3bffb1b
    li x3, 0xa3bffb1b
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    ##########################
    #MHPMCOUNTERH9 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h46dafe52} 
    ##########################
    #MHPMCOUNTERH9 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write value 0x0
    li x3, 0x0
    csrw 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write value 0x46dafe52
    li x3, 0x46dafe52
    csrw 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    ##########################
    #ICACHE testing W/R values '{'hfffffffe, 'h1, 'h55555555, 'haaaaaaaa, 'hed18a91a} 
    ##########################
    #ICACHE Write value 0xfffffffe
    li x3, 0xfffffffe
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write value 0x1
    li x3, 0x1
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write value 0x55555555
    li x3, 0x55555555
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write value 0xed18a91a
    li x3, 0xed18a91a
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    ##########################
    #MHPMEVENT16 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6afb892f} 
    ##########################
    #MHPMEVENT16 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write value 0x0
    li x3, 0x0
    csrw 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write value 0x6afb892f
    li x3, 0x6afb892f
    csrw 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    ##########################
    #MHARTID testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h76bc572a} 
    ##########################
    #MHARTID Writing data 0xffffffff to RO register/fields with mask 0xffffffff will generate exception
    #MHARTID Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xf14, x3

    #MHARTID read value
    csrr x14, 0xf14

    #MHARTID Write value 0x0
    li x3, 0x0
    csrw 0xf14, x3

    #MHARTID read value
    csrr x14, 0xf14

    #MHARTID Writing data 0x55555555 to RO register/fields with mask 0xffffffff will generate exception
    #MHARTID Write value 0x55555555
    li x3, 0x55555555
    csrw 0xf14, x3

    #MHARTID read value
    csrr x14, 0xf14

    #MHARTID Writing data 0xaaaaaaaa to RO register/fields with mask 0xffffffff will generate exception
    #MHARTID Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xf14, x3

    #MHARTID read value
    csrr x14, 0xf14

    #MHARTID Writing data 0x76bc572a to RO register/fields with mask 0xffffffff will generate exception
    #MHARTID Write value 0x76bc572a
    li x3, 0x76bc572a
    csrw 0xf14, x3

    #MHARTID read value
    csrr x14, 0xf14

    ##########################
    #MHPMCOUNTER22 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd46bffe6} 
    ##########################
    #MHPMCOUNTER22 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write value 0x0
    li x3, 0x0
    csrw 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write value 0xd46bffe6
    li x3, 0xd46bffe6
    csrw 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    ##########################
    #INSTRET testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h98b265ac} 
    ##########################
    #INSTRET Writing data 0xffffffff to RO register/fields with mask 0xffffffff will generate exception
    #INSTRET Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xc02, x3

    #INSTRET read value
    csrr x14, 0xc02

    #INSTRET Write value 0x0
    li x3, 0x0
    csrw 0xc02, x3

    #INSTRET read value
    csrr x14, 0xc02

    #INSTRET Writing data 0x55555555 to RO register/fields with mask 0xffffffff will generate exception
    #INSTRET Write value 0x55555555
    li x3, 0x55555555
    csrw 0xc02, x3

    #INSTRET read value
    csrr x14, 0xc02

    #INSTRET Writing data 0xaaaaaaaa to RO register/fields with mask 0xffffffff will generate exception
    #INSTRET Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xc02, x3

    #INSTRET read value
    csrr x14, 0xc02

    #INSTRET Writing data 0x98b265ac to RO register/fields with mask 0xffffffff will generate exception
    #INSTRET Write value 0x98b265ac
    li x3, 0x98b265ac
    csrw 0xc02, x3

    #INSTRET read value
    csrr x14, 0xc02

    ##########################
    #MHPMCOUNTER5 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd01bc4f} 
    ##########################
    #MHPMCOUNTER5 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write value 0x0
    li x3, 0x0
    csrw 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write value 0xd01bc4f
    li x3, 0xd01bc4f
    csrw 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    ##########################
    #MHPMEVENT4 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h8066911a} 
    ##########################
    #MHPMEVENT4 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write value 0x0
    li x3, 0x0
    csrw 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write value 0x8066911a
    li x3, 0x8066911a
    csrw 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    ##########################
    #MHPMCOUNTER7 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc62f86af} 
    ##########################
    #MHPMCOUNTER7 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write value 0x0
    li x3, 0x0
    csrw 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write value 0xc62f86af
    li x3, 0xc62f86af
    csrw 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    ##########################
    #PMPADDR12 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h79a5d205} 
    ##########################
    #PMPADDR12 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write value 0x0
    li x3, 0x0
    csrw 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write value 0x79a5d205
    li x3, 0x79a5d205
    csrw 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    ##########################
    #PMPADDR11 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h170899e0} 
    ##########################
    #PMPADDR11 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write value 0x0
    li x3, 0x0
    csrw 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write value 0x170899e0
    li x3, 0x170899e0
    csrw 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    ##########################
    #MHPMEVENT22 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcc0edf43} 
    ##########################
    #MHPMEVENT22 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write value 0x0
    li x3, 0x0
    csrw 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write value 0xcc0edf43
    li x3, 0xcc0edf43
    csrw 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    ##########################
    #MHPMCOUNTERH17 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hff3f4053} 
    ##########################
    #MHPMCOUNTERH17 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write value 0x0
    li x3, 0x0
    csrw 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write value 0xff3f4053
    li x3, 0xff3f4053
    csrw 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    ##########################
    #PMPADDR15 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6d010fb0} 
    ##########################
    #PMPADDR15 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write value 0x0
    li x3, 0x0
    csrw 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write value 0x6d010fb0
    li x3, 0x6d010fb0
    csrw 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    ##########################
    #MHPMCOUNTERH4 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h24baafce} 
    ##########################
    #MHPMCOUNTERH4 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write value 0x0
    li x3, 0x0
    csrw 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write value 0x24baafce
    li x3, 0x24baafce
    csrw 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    ##########################
    #MVENDORID testing W/R values '{'hffff3fbf, 'hc040, 'h55555555, 'haaaaaaaa, 'h49c2df61} 
    ##########################
    #MVENDORID Writing data 0xfffff9fd to RO register/fields with mask 0xffffffff will generate exception
    #MVENDORID Write value 0xfffff9fd
    li x3, 0xffff3fbf
    csrw 0xf11, x3

    #MVENDORID read value
    csrr x14, 0xf11

    #MVENDORID Writing data 0x0602 to RO register/fields with mask 0xffffffff will generate exception
    #MVENDORID Write value 0x0602
    li x3, 0x0602
    csrw 0xf11, x3

    #MVENDORID read value
    csrr x14, 0xf11

    #MVENDORID Writing data 0x55555555 to RO register/fields with mask 0xffffffff will generate exception
    #MVENDORID Write value 0x55555555
    li x3, 0x55555555
    csrw 0xf11, x3

    #MVENDORID read value
    csrr x14, 0xf11

    #MVENDORID Writing data 0xaaaaaaaa to RO register/fields with mask 0xffffffff will generate exception
    #MVENDORID Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xf11, x3

    #MVENDORID read value
    csrr x14, 0xf11

    #MVENDORID Writing data 0x49c2df61 to RO register/fields with mask 0xffffffff will generate exception
    #MVENDORID Write value 0x49c2df61
    li x3, 0x49c2df61
    csrw 0xf11, x3

    #MVENDORID read value
    csrr x14, 0xf11

    ##########################
    #MIP testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbcdb1adb} 
    ##########################
    #MIP Writing data 0xffffffff to RO register/fields with mask 0x888 will generate exception
    #MIP Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x55555555
    li x3, 0x55555555
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Writing data 0xaaaaaaaa to RO register/fields with mask 0x888 will generate exception
    #MIP Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Writing data 0xbcdb1adb to RO register/fields with mask 0x888 will generate exception
    #MIP Write value 0xbcdb1adb
    li x3, 0xbcdb1adb
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #Clear MIP to avoid traping
    csrw 0x344, x0

    #MIP read value
    csrr x14, 0x344
    ##########################
    #PMPADDR3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hf479076} 
    ##########################
    #PMPADDR3 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write value 0x0
    li x3, 0x0
    csrw 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write value 0xf479076
    li x3, 0xf479076
    csrw 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    ##########################
    #MHPMCOUNTER31 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h15841a89} 
    ##########################
    #MHPMCOUNTER31 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write value 0x0
    li x3, 0x0
    csrw 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write value 0x15841a89
    li x3, 0x15841a89
    csrw 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    ##########################
    #MINSTRET testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4db48383} 
    ##########################
    #MINSTRET Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write value 0x0
    li x3, 0x0
    csrw 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write value 0x4db48383
    li x3, 0x4db48383
    csrw 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    ##########################
    #MHPMCOUNTERH21 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h29f48d24} 
    ##########################
    #MHPMCOUNTERH21 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write value 0x0
    li x3, 0x0
    csrw 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write value 0x29f48d24
    li x3, 0x29f48d24
    csrw 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    ##########################
    #CYCLE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h11e4889b} 
    ##########################
    #CYCLE Writing data 0xffffffff to RO register/fields with mask 0xffffffff will generate exception
    #CYCLE Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xc00, x3

    #CYCLE read value
    csrr x14, 0xc00

    #CYCLE Write value 0x0
    li x3, 0x0
    csrw 0xc00, x3

    #CYCLE read value
    csrr x14, 0xc00

    #CYCLE Writing data 0x55555555 to RO register/fields with mask 0xffffffff will generate exception
    #CYCLE Write value 0x55555555
    li x3, 0x55555555
    csrw 0xc00, x3

    #CYCLE read value
    csrr x14, 0xc00

    #CYCLE Writing data 0xaaaaaaaa to RO register/fields with mask 0xffffffff will generate exception
    #CYCLE Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xc00, x3

    #CYCLE read value
    csrr x14, 0xc00

    #CYCLE Writing data 0x11e4889b to RO register/fields with mask 0xffffffff will generate exception
    #CYCLE Write value 0x11e4889b
    li x3, 0x11e4889b
    csrw 0xc00, x3

    #CYCLE read value
    csrr x14, 0xc00

    ##########################
    #MHPMCOUNTER6 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h28ee3ea5} 
    ##########################
    #MHPMCOUNTER6 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write value 0x0
    li x3, 0x0
    csrw 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write value 0x28ee3ea5
    li x3, 0x28ee3ea5
    csrw 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    ##########################
    #PMPADDR10 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h68892df7} 
    ##########################
    #PMPADDR10 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write value 0x0
    li x3, 0x0
    csrw 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write value 0x68892df7
    li x3, 0x68892df7
    csrw 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    ##########################
    #MHPMCOUNTERH11 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h1ffe0c6a} 
    ##########################
    #MHPMCOUNTERH11 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write value 0x0
    li x3, 0x0
    csrw 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write value 0x1ffe0c6a
    li x3, 0x1ffe0c6a
    csrw 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    ##########################
    #PMPCFG0 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbf40ebb2} 
    ##########################
    #PMPCFG0 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x0
    li x3, 0x0
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xbf40ebb2
    li x3, 0xbf40ebb2
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    ##########################
    #PMPADDR5 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h8c0e5e3f} 
    ##########################
    #PMPADDR5 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write value 0x0
    li x3, 0x0
    csrw 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write value 0x8c0e5e3f
    li x3, 0x8c0e5e3f
    csrw 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    ##########################
    #MHPMCOUNTERH8 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h8b79a6e0} 
    ##########################
    #MHPMCOUNTERH8 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write value 0x0
    li x3, 0x0
    csrw 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write value 0x8b79a6e0
    li x3, 0x8b79a6e0
    csrw 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    ##########################
    #MHPMEVENT14 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h76cdf0b6} 
    ##########################
    #MHPMEVENT14 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write value 0x0
    li x3, 0x0
    csrw 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write value 0x76cdf0b6
    li x3, 0x76cdf0b6
    csrw 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    ##########################
    #MHPMEVENT7 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5393807d} 
    ##########################
    #MHPMEVENT7 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write value 0x0
    li x3, 0x0
    csrw 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write value 0x5393807d
    li x3, 0x5393807d
    csrw 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    ##########################
    #PMPADDR13 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3f67cf91} 
    ##########################
    #PMPADDR13 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write value 0x0
    li x3, 0x0
    csrw 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write value 0x3f67cf91
    li x3, 0x3f67cf91
    csrw 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    ##########################
    #CYCLEH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3e88e3b} 
    ##########################
    #CYCLEH Writing data 0xffffffff to RO register/fields with mask 0xffffffff will generate exception
    #CYCLEH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xc80, x3

    #CYCLEH read value
    csrr x14, 0xc80

    #CYCLEH Write value 0x0
    li x3, 0x0
    csrw 0xc80, x3

    #CYCLEH read value
    csrr x14, 0xc80

    #CYCLEH Writing data 0x55555555 to RO register/fields with mask 0xffffffff will generate exception
    #CYCLEH Write value 0x55555555
    li x3, 0x55555555
    csrw 0xc80, x3

    #CYCLEH read value
    csrr x14, 0xc80

    #CYCLEH Writing data 0xaaaaaaaa to RO register/fields with mask 0xffffffff will generate exception
    #CYCLEH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xc80, x3

    #CYCLEH read value
    csrr x14, 0xc80

    #CYCLEH Writing data 0x3e88e3b to RO register/fields with mask 0xffffffff will generate exception
    #CYCLEH Write value 0x3e88e3b
    li x3, 0x3e88e3b
    csrw 0xc80, x3

    #CYCLEH read value
    csrr x14, 0xc80

    ##########################
    #MHPMCOUNTER26 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdae36d6b} 
    ##########################
    #MHPMCOUNTER26 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write value 0x0
    li x3, 0x0
    csrw 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write value 0xdae36d6b
    li x3, 0xdae36d6b
    csrw 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    ##########################
    #MHPMCOUNTER17 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2d74f356} 
    ##########################
    #MHPMCOUNTER17 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write value 0x0
    li x3, 0x0
    csrw 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write value 0x2d74f356
    li x3, 0x2d74f356
    csrw 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    ##########################
    #PMPCFG1 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha725592e} 
    ##########################
    #PMPCFG1 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x0
    li x3, 0x0
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0xa725592e
    li x3, 0xa725592e
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    ##########################
    #MHPMEVENT5 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he2e64cdc} 
    ##########################
    #MHPMEVENT5 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write value 0x0
    li x3, 0x0
    csrw 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write value 0xe2e64cdc
    li x3, 0xe2e64cdc
    csrw 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    ##########################
    #MHPMCOUNTERH13 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5567e51c} 
    ##########################
    #MHPMCOUNTERH13 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write value 0x0
    li x3, 0x0
    csrw 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write value 0x5567e51c
    li x3, 0x5567e51c
    csrw 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    ##########################
    #MHPMCOUNTER30 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7f5e3f2} 
    ##########################
    #MHPMCOUNTER30 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write value 0x0
    li x3, 0x0
    csrw 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write value 0x7f5e3f2
    li x3, 0x7f5e3f2
    csrw 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    ##########################
    #MINSTRETH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hf829d895} 
    ##########################
    #MINSTRETH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write value 0x0
    li x3, 0x0
    csrw 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write value 0xf829d895
    li x3, 0xf829d895
    csrw 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    ##########################
    #INSTRETH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hab00d183} 
    ##########################
    #INSTRETH Writing data 0xffffffff to RO register/fields with mask 0xffffffff will generate exception
    #INSTRETH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xc82, x3

    #INSTRETH read value
    csrr x14, 0xc82

    #INSTRETH Write value 0x0
    li x3, 0x0
    csrw 0xc82, x3

    #INSTRETH read value
    csrr x14, 0xc82

    #INSTRETH Writing data 0x55555555 to RO register/fields with mask 0xffffffff will generate exception
    #INSTRETH Write value 0x55555555
    li x3, 0x55555555
    csrw 0xc82, x3

    #INSTRETH read value
    csrr x14, 0xc82

    #INSTRETH Writing data 0xaaaaaaaa to RO register/fields with mask 0xffffffff will generate exception
    #INSTRETH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xc82, x3

    #INSTRETH read value
    csrr x14, 0xc82

    #INSTRETH Writing data 0xab00d183 to RO register/fields with mask 0xffffffff will generate exception
    #INSTRETH Write value 0xab00d183
    li x3, 0xab00d183
    csrw 0xc82, x3

    #INSTRETH read value
    csrr x14, 0xc82

    ##########################
    #MHPMEVENT8 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb906536e} 
    ##########################
    #MHPMEVENT8 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write value 0x0
    li x3, 0x0
    csrw 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write value 0xb906536e
    li x3, 0xb906536e
    csrw 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    ##########################
    #MHPMCOUNTERH24 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb9887c0a} 
    ##########################
    #MHPMCOUNTERH24 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write value 0x0
    li x3, 0x0
    csrw 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write value 0xb9887c0a
    li x3, 0xb9887c0a
    csrw 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    ##########################
    #MHPMEVENT20 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcb816ebc} 
    ##########################
    #MHPMEVENT20 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write value 0x0
    li x3, 0x0
    csrw 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write value 0xcb816ebc
    li x3, 0xcb816ebc
    csrw 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    ##########################
    #MHPMCOUNTERH5 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hf736921e} 
    ##########################
    #MHPMCOUNTERH5 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write value 0x0
    li x3, 0x0
    csrw 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write value 0xf736921e
    li x3, 0xf736921e
    csrw 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    ##########################
    #PMPADDR9 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5aed1c94} 
    ##########################
    #PMPADDR9 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write value 0x0
    li x3, 0x0
    csrw 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write value 0x5aed1c94
    li x3, 0x5aed1c94
    csrw 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    ##########################
    #MHPMEVENT10 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h1a3a0196} 
    ##########################
    #MHPMEVENT10 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write value 0x0
    li x3, 0x0
    csrw 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write value 0x1a3a0196
    li x3, 0x1a3a0196
    csrw 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    ##########################
    #PMPADDR7 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he85e10a2} 
    ##########################
    #PMPADDR7 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write value 0x0
    li x3, 0x0
    csrw 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write value 0xe85e10a2
    li x3, 0xe85e10a2
    csrw 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    ##########################
    #PMPADDR8 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h71513c7b} 
    ##########################
    #PMPADDR8 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write value 0x0
    li x3, 0x0
    csrw 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write value 0x71513c7b
    li x3, 0x71513c7b
    csrw 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    ##########################
    #MHPMCOUNTERH7 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h73bf0545} 
    ##########################
    #MHPMCOUNTERH7 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write value 0x0
    li x3, 0x0
    csrw 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write value 0x73bf0545
    li x3, 0x73bf0545
    csrw 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    ##########################
    #PMPADDR14 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h14d57858} 
    ##########################
    #PMPADDR14 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write value 0x0
    li x3, 0x0
    csrw 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write value 0x14d57858
    li x3, 0x14d57858
    csrw 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    ##########################
    #MHPMEVENT13 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h80a61c67} 
    ##########################
    #MHPMEVENT13 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write value 0x0
    li x3, 0x0
    csrw 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write value 0x80a61c67
    li x3, 0x80a61c67
    csrw 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    ##########################
    #MHPMCOUNTER14 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he604b325} 
    ##########################
    #MHPMCOUNTER14 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write value 0x0
    li x3, 0x0
    csrw 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write value 0xe604b325
    li x3, 0xe604b325
    csrw 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    ##########################
    #MHPMCOUNTER13 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb38df3ec} 
    ##########################
    #MHPMCOUNTER13 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write value 0x0
    li x3, 0x0
    csrw 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write value 0xb38df3ec
    li x3, 0xb38df3ec
    csrw 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    ##########################
    #MHPMCOUNTERH30 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9476228} 
    ##########################
    #MHPMCOUNTERH30 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write value 0x0
    li x3, 0x0
    csrw 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write value 0x9476228
    li x3, 0x9476228
    csrw 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    ##########################
    #MSTATUS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h77a27366} 
    ##########################
    #MSTATUS Writing data 0xffffffff to RO register/fields with mask 0x8001e600 will generate exception
    #MSTATUS Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Writing data 0x55555555 to RO register/fields with mask 0x8001e600 will generate exception
    #MSTATUS Write value 0x55555555
    li x3, 0x55555555
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Writing data 0xaaaaaaaa to RO register/fields with mask 0x8001e600 will generate exception
    #MSTATUS Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Writing data 0x77a27366 to RO register/fields with mask 0x8001e600 will generate exception
    #MSTATUS Write value 0x77a27366
    li x3, 0x77a27366
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    ##########################
    #MHPMCOUNTER15 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hedba9ca1} 
    ##########################
    #MHPMCOUNTER15 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write value 0x0
    li x3, 0x0
    csrw 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write value 0xedba9ca1
    li x3, 0xedba9ca1
    csrw 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    ##########################
    #MHPMCOUNTER16 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3b6da8b8} 
    ##########################
    #MHPMCOUNTER16 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write value 0x0
    li x3, 0x0
    csrw 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write value 0x3b6da8b8
    li x3, 0x3b6da8b8
    csrw 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    ##########################
    #MHPMEVENT25 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdbf66b7c} 
    ##########################
    #MHPMEVENT25 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write value 0x0
    li x3, 0x0
    csrw 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write value 0xdbf66b7c
    li x3, 0xdbf66b7c
    csrw 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    ##########################
    #MHPMEVENT12 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc902a15d} 
    ##########################
    #MHPMEVENT12 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write value 0x0
    li x3, 0x0
    csrw 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write value 0xc902a15d
    li x3, 0xc902a15d
    csrw 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    ##########################
    #MHPMEVENT21 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbe6a6fe6} 
    ##########################
    #MHPMEVENT21 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write value 0x0
    li x3, 0x0
    csrw 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write value 0xbe6a6fe6
    li x3, 0xbe6a6fe6
    csrw 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    ##########################
    #MHPMCOUNTERH20 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcffc2951} 
    ##########################
    #MHPMCOUNTERH20 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write value 0x0
    li x3, 0x0
    csrw 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write value 0xcffc2951
    li x3, 0xcffc2951
    csrw 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    ##########################
    #MHPMEVENT17 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbe854762} 
    ##########################
    #MHPMEVENT17 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write value 0x0
    li x3, 0x0
    csrw 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write value 0xbe854762
    li x3, 0xbe854762
    csrw 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    ##########################
    #MHPMCOUNTERH23 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h41debf34} 
    ##########################
    #MHPMCOUNTERH23 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write value 0x0
    li x3, 0x0
    csrw 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write value 0x41debf34
    li x3, 0x41debf34
    csrw 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    ##########################
    #MHPMEVENT11 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he3a79f09} 
    ##########################
    #MHPMEVENT11 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write value 0x0
    li x3, 0x0
    csrw 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write value 0xe3a79f09
    li x3, 0xe3a79f09
    csrw 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    ##########################
    #MHPMCOUNTER12 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h50962a82} 
    ##########################
    #MHPMCOUNTER12 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write value 0x0
    li x3, 0x0
    csrw 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write value 0x50962a82
    li x3, 0x50962a82
    csrw 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    ##########################
    #MHPMCOUNTER18 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h48631e01} 
    ##########################
    #MHPMCOUNTER18 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write value 0x0
    li x3, 0x0
    csrw 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write value 0x48631e01
    li x3, 0x48631e01
    csrw 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    ##########################
    #MHPMCOUNTERH18 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5df43730} 
    ##########################
    #MHPMCOUNTERH18 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write value 0x0
    li x3, 0x0
    csrw 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write value 0x5df43730
    li x3, 0x5df43730
    csrw 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    ##########################
    #MHPMEVENT31 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h178e0640} 
    ##########################
    #MHPMEVENT31 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write value 0x0
    li x3, 0x0
    csrw 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write value 0x178e0640
    li x3, 0x178e0640
    csrw 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    ##########################
    #PMPADDR0 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h93d7ddfa} 
    ##########################
    #PMPADDR0 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write value 0x0
    li x3, 0x0
    csrw 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write value 0x93d7ddfa
    li x3, 0x93d7ddfa
    csrw 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    ##########################
    #MHPMCOUNTERH26 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h26cbfdd3} 
    ##########################
    #MHPMCOUNTERH26 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write value 0x0
    li x3, 0x0
    csrw 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write value 0x26cbfdd3
    li x3, 0x26cbfdd3
    csrw 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    ##########################
    #PMPADDR2 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4e68e8a3} 
    ##########################
    #PMPADDR2 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write value 0x0
    li x3, 0x0
    csrw 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write value 0x4e68e8a3
    li x3, 0x4e68e8a3
    csrw 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    ##########################
    #MHPMCOUNTER4 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h18c2ccea} 
    ##########################
    #MHPMCOUNTER4 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write value 0x0
    li x3, 0x0
    csrw 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write value 0x18c2ccea
    li x3, 0x18c2ccea
    csrw 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    ##########################
    #MHPMEVENT15 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h1d2057b6} 
    ##########################
    #MHPMEVENT15 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write value 0x0
    li x3, 0x0
    csrw 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write value 0x1d2057b6
    li x3, 0x1d2057b6
    csrw 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    ##########################
    #MHPMCOUNTERH31 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h43a9779e} 
    ##########################
    #MHPMCOUNTERH31 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write value 0x0
    li x3, 0x0
    csrw 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write value 0x43a9779e
    li x3, 0x43a9779e
    csrw 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    ##########################
    #MHPMCOUNTERH16 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha84f30ee} 
    ##########################
    #MHPMCOUNTERH16 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write value 0x0
    li x3, 0x0
    csrw 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write value 0xa84f30ee
    li x3, 0xa84f30ee
    csrw 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    ##########################
    #MHPMCOUNTERH10 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9342daa1} 
    ##########################
    #MHPMCOUNTERH10 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write value 0x0
    li x3, 0x0
    csrw 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write value 0x9342daa1
    li x3, 0x9342daa1
    csrw 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    ##########################
    #MHPMEVENT3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hca14d21d} 
    ##########################
    #MHPMEVENT3 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write value 0x0
    li x3, 0x0
    csrw 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write value 0xca14d21d
    li x3, 0xca14d21d
    csrw 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    ##########################
    #MHPMEVENT18 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3dea50fd} 
    ##########################
    #MHPMEVENT18 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write value 0x0
    li x3, 0x0
    csrw 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write value 0x3dea50fd
    li x3, 0x3dea50fd
    csrw 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    ##########################
    #MHPMCOUNTERH28 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h169b598c} 
    ##########################
    #MHPMCOUNTERH28 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write value 0x0
    li x3, 0x0
    csrw 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write value 0x169b598c
    li x3, 0x169b598c
    csrw 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    ##########################
    #MHPMCOUNTERH19 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha192df7f} 
    ##########################
    #MHPMCOUNTERH19 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write value 0x0
    li x3, 0x0
    csrw 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write value 0xa192df7f
    li x3, 0xa192df7f
    csrw 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    ##########################
    #PMPADDR4 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h38f28a23} 
    ##########################
    #PMPADDR4 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write value 0x0
    li x3, 0x0
    csrw 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write value 0x38f28a23
    li x3, 0x38f28a23
    csrw 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    ##########################
    #MHPMCOUNTER10 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h1a89ca32} 
    ##########################
    #MHPMCOUNTER10 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write value 0x0
    li x3, 0x0
    csrw 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write value 0x1a89ca32
    li x3, 0x1a89ca32
    csrw 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    ##########################
    #MCYCLEH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd6bfeb4b} 
    ##########################
    #MCYCLEH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write value 0x0
    li x3, 0x0
    csrw 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write value 0xd6bfeb4b
    li x3, 0xd6bfeb4b
    csrw 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    ##########################
    #MCAUSE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdceb655} 
    ##########################
    #MCAUSE Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0x0
    li x3, 0x0
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0x55555555
    li x3, 0x55555555
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0xdceb655
    li x3, 0xdceb655
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    ##########################
    #PMPADDR1 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdb1e5f73} 
    ##########################
    #PMPADDR1 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write value 0x0
    li x3, 0x0
    csrw 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write value 0xdb1e5f73
    li x3, 0xdb1e5f73
    csrw 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    ##########################
    #MISA testing W/R values '{'hfdbf7bfb, 'h2408404, 'h55555555, 'haaaaaaaa, 'h53086dae} 
    ##########################
    #MISA Write value 0xfdbf7bfb
    li x3, 0xfdbf7bfb
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x2408404
    li x3, 0x2408404
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x55555555
    li x3, 0x55555555
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x53086dae
    li x3, 0x53086dae
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    ##########################
    #MIMPID testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hecaf64b8} 
    ##########################
    #MIMPID Writing data 0xffffffff to RO register/fields with mask 0xffffffff will generate exception
    #MIMPID Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xf13, x3

    #MIMPID read value
    csrr x14, 0xf13

    #MIMPID Write value 0x0
    li x3, 0x0
    csrw 0xf13, x3

    #MIMPID read value
    csrr x14, 0xf13

    #MIMPID Writing data 0x55555555 to RO register/fields with mask 0xffffffff will generate exception
    #MIMPID Write value 0x55555555
    li x3, 0x55555555
    csrw 0xf13, x3

    #MIMPID read value
    csrr x14, 0xf13

    #MIMPID Writing data 0xaaaaaaaa to RO register/fields with mask 0xffffffff will generate exception
    #MIMPID Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xf13, x3

    #MIMPID read value
    csrr x14, 0xf13

    #MIMPID Writing data 0xecaf64b8 to RO register/fields with mask 0xffffffff will generate exception
    #MIMPID Write value 0xecaf64b8
    li x3, 0xecaf64b8
    csrw 0xf13, x3

    #MIMPID read value
    csrr x14, 0xf13

    ##########################
    #MHPMCOUNTER19 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hce3f7a09} 
    ##########################
    #MHPMCOUNTER19 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write value 0x0
    li x3, 0x0
    csrw 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write value 0xce3f7a09
    li x3, 0xce3f7a09
    csrw 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    ##########################
    #MHPMCOUNTERH15 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb5cb0a55} 
    ##########################
    #MHPMCOUNTERH15 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write value 0x0
    li x3, 0x0
    csrw 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write value 0xb5cb0a55
    li x3, 0xb5cb0a55
    csrw 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    ##########################
    #MHPMEVENT30 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h60c96d80} 
    ##########################
    #MHPMEVENT30 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write value 0x0
    li x3, 0x0
    csrw 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write value 0x60c96d80
    li x3, 0x60c96d80
    csrw 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    ##########################
    #MHPMEVENT6 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7acc3380} 
    ##########################
    #MHPMEVENT6 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write value 0x0
    li x3, 0x0
    csrw 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write value 0x7acc3380
    li x3, 0x7acc3380
    csrw 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    ##########################
    #MHPMCOUNTER8 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd22007f2} 
    ##########################
    #MHPMCOUNTER8 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write value 0x0
    li x3, 0x0
    csrw 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write value 0xd22007f2
    li x3, 0xd22007f2
    csrw 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    ##########################
    #MHPMCOUNTER28 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3ba14b9b} 
    ##########################
    #MHPMCOUNTER28 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write value 0x0
    li x3, 0x0
    csrw 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write value 0x3ba14b9b
    li x3, 0x3ba14b9b
    csrw 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    ##########################
    #MHPMEVENT28 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb6577853} 
    ##########################
    #MHPMEVENT28 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write value 0x0
    li x3, 0x0
    csrw 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write value 0xb6577853
    li x3, 0xb6577853
    csrw 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    ##########################
    #MHPMCOUNTER27 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h828fc44c} 
    ##########################
    #MHPMCOUNTER27 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write value 0x0
    li x3, 0x0
    csrw 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write value 0x828fc44c
    li x3, 0x828fc44c
    csrw 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    ##########################
    #MCYCLE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he72a0ebb} 
    ##########################
    #MCYCLE Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write value 0x0
    li x3, 0x0
    csrw 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write value 0xe72a0ebb
    li x3, 0xe72a0ebb
    csrw 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    ##########################
    #MHPMCOUNTERH6 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h654e8886} 
    ##########################
    #MHPMCOUNTERH6 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write value 0x0
    li x3, 0x0
    csrw 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write value 0x654e8886
    li x3, 0x654e8886
    csrw 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    ##########################
    #MHPMCOUNTER3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbc971684} 
    ##########################
    #MHPMCOUNTER3 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write value 0x0
    li x3, 0x0
    csrw 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write value 0xbc971684
    li x3, 0xbc971684
    csrw 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    ##########################
    #MHPMCOUNTERH25 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hab420d33} 
    ##########################
    #MHPMCOUNTERH25 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write value 0x0
    li x3, 0x0
    csrw 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write value 0xab420d33
    li x3, 0xab420d33
    csrw 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    ##########################
    #MHPMCOUNTER21 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h55a154a6} 
    ##########################
    #MHPMCOUNTER21 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write value 0x0
    li x3, 0x0
    csrw 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write value 0x55a154a6
    li x3, 0x55a154a6
    csrw 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    ##########################
    #MHPMEVENT19 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h44885caa} 
    ##########################
    #MHPMEVENT19 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write value 0x0
    li x3, 0x0
    csrw 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write value 0x44885caa
    li x3, 0x44885caa
    csrw 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    ##########################
    #MEPC testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he54ec0d} 
    ##########################
    #MEPC Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write value 0x0
    li x3, 0x0
    csrw 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write value 0x55555555
    li x3, 0x55555555
    csrw 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write value 0xe54ec0d
    li x3, 0xe54ec0d
    csrw 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    ##########################
    #MHPMEVENT9 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb0197d41} 
    ##########################
    #MHPMEVENT9 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write value 0x0
    li x3, 0x0
    csrw 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write value 0xb0197d41
    li x3, 0xb0197d41
    csrw 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    ##########################
    #MHPMCOUNTER20 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h16642428} 
    ##########################
    #MHPMCOUNTER20 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write value 0x0
    li x3, 0x0
    csrw 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write value 0x16642428
    li x3, 0x16642428
    csrw 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    ##########################
    #MHPMEVENT26 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfed241a6} 
    ##########################
    #MHPMEVENT26 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write value 0x0
    li x3, 0x0
    csrw 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write value 0xfed241a6
    li x3, 0xfed241a6
    csrw 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    ##########################
    #MHPMCOUNTERH14 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9e24b5a0} 
    ##########################
    #MHPMCOUNTERH14 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write value 0x0
    li x3, 0x0
    csrw 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write value 0x9e24b5a0
    li x3, 0x9e24b5a0
    csrw 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    ##########################
    #MHPMCOUNTERH22 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h997c0cac} 
    ##########################
    #MHPMCOUNTERH22 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write value 0x0
    li x3, 0x0
    csrw 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write value 0x997c0cac
    li x3, 0x997c0cac
    csrw 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    ##########################
    #MHPMCOUNTERH3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he041cf87} 
    ##########################
    #MHPMCOUNTERH3 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write value 0x0
    li x3, 0x0
    csrw 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write value 0xe041cf87
    li x3, 0xe041cf87
    csrw 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    ##########################
    #MHPMCOUNTERH29 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h11b3403f} 
    ##########################
    #MHPMCOUNTERH29 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write value 0x0
    li x3, 0x0
    csrw 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write value 0x11b3403f
    li x3, 0x11b3403f
    csrw 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    ##########################
    #MSCRATCH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcb476e0a} 
    ##########################
    #MSCRATCH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write value 0x0
    li x3, 0x0
    csrw 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write value 0x55555555
    li x3, 0x55555555
    csrw 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write value 0xcb476e0a
    li x3, 0xcb476e0a
    csrw 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    ##########################
    #MHPMCOUNTER11 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7f68b2b3} 
    ##########################
    #MHPMCOUNTER11 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write value 0x0
    li x3, 0x0
    csrw 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write value 0x7f68b2b3
    li x3, 0x7f68b2b3
    csrw 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    ##########################
    #MSTATUSH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9950019a} 
    ##########################
    #MSTATUSH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x0
    li x3, 0x0
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x55555555
    li x3, 0x55555555
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x9950019a
    li x3, 0x9950019a
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    ##########################
    #MHPMCOUNTER9 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcd0f8916} 
    ##########################
    #MHPMCOUNTER9 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write value 0x0
    li x3, 0x0
    csrw 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write value 0xcd0f8916
    li x3, 0xcd0f8916
    csrw 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    ##########################
    #PMPADDR6 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6d9dd474} 
    ##########################
    #PMPADDR6 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write value 0x0
    li x3, 0x0
    csrw 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write value 0x6d9dd474
    li x3, 0x6d9dd474
    csrw 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    ##########################
    #MHPMCOUNTER24 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha48831d8} 
    ##########################
    #MHPMCOUNTER24 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write value 0x0
    li x3, 0x0
    csrw 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write value 0xa48831d8
    li x3, 0xa48831d8
    csrw 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    ##########################
    #MHPMEVENT27 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb6faaf18} 
    ##########################
    #MHPMEVENT27 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write value 0x0
    li x3, 0x0
    csrw 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write value 0xb6faaf18
    li x3, 0xb6faaf18
    csrw 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    ##########################
    #MARCHID testing W/R values '{'hfffffffc, 'h3, 'h55555555, 'haaaaaaaa, 'h9ad6f2e7} 
    ##########################
    #MARCHID Writing data 0xfffffffc to RO register/fields with mask 0xffffffff will generate exception
    #MARCHID Write value 0xfffffffc
    li x3, 0xfffffffc
    csrw 0xf12, x3

    #MARCHID read value
    csrr x14, 0xf12

    #MARCHID Writing data 0x3 to RO register/fields with mask 0xffffffff will generate exception
    #MARCHID Write value 0x3
    li x3, 0x3
    csrw 0xf12, x3

    #MARCHID read value
    csrr x14, 0xf12

    #MARCHID Writing data 0x55555555 to RO register/fields with mask 0xffffffff will generate exception
    #MARCHID Write value 0x55555555
    li x3, 0x55555555
    csrw 0xf12, x3

    #MARCHID read value
    csrr x14, 0xf12

    #MARCHID Writing data 0xaaaaaaaa to RO register/fields with mask 0xffffffff will generate exception
    #MARCHID Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xf12, x3

    #MARCHID read value
    csrr x14, 0xf12

    #MARCHID Writing data 0x9ad6f2e7 to RO register/fields with mask 0xffffffff will generate exception
    #MARCHID Write value 0x9ad6f2e7
    li x3, 0x9ad6f2e7
    csrw 0xf12, x3

    #MARCHID read value
    csrr x14, 0xf12

    ##########################
    #PMPCFG3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9dfea3e6} 
    ##########################
    #PMPCFG3 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x0
    li x3, 0x0
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x9dfea3e6
    li x3, 0x9dfea3e6
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    ##########################
    #MTVAL testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb988b0b3} 
    ##########################
    #MTVAL Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write value 0x0
    li x3, 0x0
    csrw 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write value 0x55555555
    li x3, 0x55555555
    csrw 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write value 0xb988b0b3
    li x3, 0xb988b0b3
    csrw 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    ##########################
    #MHPMEVENT23 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h45640b94} 
    ##########################
    #MHPMEVENT23 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write value 0x0
    li x3, 0x0
    csrw 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write value 0x55555555
    li x3, 0x55555555
    csrw 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write value 0x45640b94
    li x3, 0x45640b94
    csrw 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    ##########################
    #MHPMCOUNTER29 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfd77ff67} 
    ##########################
    #MHPMCOUNTER29 Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write value 0x0
    li x3, 0x0
    csrw 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write value 0xfd77ff67
    li x3, 0xfd77ff67
    csrw 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d


    #End of csr test
    j csr_pass

csr_pass:
    li x1, 0xBEEFBEEF
    li x1, 0
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop: j self_loop

csr_fail:
    li x1, 0xBADBAD
    li x1, 1
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop_2: j self_loop_2

.align 8
exception_handler:
    # increment return address to skip instruction generating the exception
    # valid only if faulting instruction is not compressed (4-byte long)
    csrr    x30, mepc  # mepc: 0x341
    addi    x30, x30, 4
    csrw    mepc, x30  # mepc: 0x341
    mret

