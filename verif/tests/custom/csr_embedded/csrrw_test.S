# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

csrrw:
    #Start CSR tests: Write/Read all RW registers in a random order
    #User ignored registers: 

    #MHARTID WR skipped since it's a RO register

    ##########################
    #MHPMEVENT12 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h775277de} 
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

    #MHPMEVENT12 Write value 0x775277de
    li x3, 0x775277de
    csrw 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    ##########################
    #ICACHE testing W/R values '{'hfffffffe, 'h1, 'h55555555, 'haaaaaaaa, 'h8420e43c} 
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

    #ICACHE Write value 0x8420e43c
    li x3, 0x8420e43c
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    ##########################
    #MSTATUSH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4aa1c50c} 
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

    #MSTATUSH Write value 0x4aa1c50c
    li x3, 0x4aa1c50c
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    ##########################
    #MIE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4670c13a} 
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

    #MIE Write value 0x4670c13a
    li x3, 0x4670c13a
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    ##########################
    #MHPMCOUNTER30 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc3d3eaf7} 
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

    #MHPMCOUNTER30 Write value 0xc3d3eaf7
    li x3, 0xc3d3eaf7
    csrw 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    ##########################
    #MHPMEVENT16 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h335a76bc} 
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

    #MHPMEVENT16 Write value 0x335a76bc
    li x3, 0x335a76bc
    csrw 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    ##########################
    #MCYCLEH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h29aa60fc} 
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

    #MCYCLEH Write value 0x29aa60fc
    li x3, 0x29aa60fc
    csrw 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    ##########################
    #PMPADDR12 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h43738427} 
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

    #PMPADDR12 Write value 0x43738427
    li x3, 0x43738427
    csrw 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    ##########################
    #PMPADDR8 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hceb1df14} 
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

    #PMPADDR8 Write value 0xceb1df14
    li x3, 0xceb1df14
    csrw 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #INSTRET WR skipped since it's a RO register

    ##########################
    #PMPADDR9 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfa0c0999} 
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

    #PMPADDR9 Write value 0xfa0c0999
    li x3, 0xfa0c0999
    csrw 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #INSTRETH WR skipped since it's a RO register

    ##########################
    #MHPMEVENT9 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h81e78126} 
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

    #MHPMEVENT9 Write value 0x81e78126
    li x3, 0x81e78126
    csrw 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    ##########################
    #MHPMCOUNTERH17 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2b8259f8} 
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

    #MHPMCOUNTERH17 Write value 0x2b8259f8
    li x3, 0x2b8259f8
    csrw 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    ##########################
    #MHPMEVENT6 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hccd50781} 
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

    #MHPMEVENT6 Write value 0xccd50781
    li x3, 0xccd50781
    csrw 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    ##########################
    #MSCRATCH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h886bd5e6} 
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

    #MSCRATCH Write value 0x886bd5e6
    li x3, 0x886bd5e6
    csrw 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    ##########################
    #MHPMCOUNTER25 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'haceac9a7} 
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

    #MHPMCOUNTER25 Write value 0xaceac9a7
    li x3, 0xaceac9a7
    csrw 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MVENDORID WR skipped since it's a RO register

    ##########################
    #MHPMEVENT8 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3883bd23} 
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

    #MHPMEVENT8 Write value 0x3883bd23
    li x3, 0x3883bd23
    csrw 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    ##########################
    #MHPMEVENT20 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdf7cb658} 
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

    #MHPMEVENT20 Write value 0xdf7cb658
    li x3, 0xdf7cb658
    csrw 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    ##########################
    #MHPMCOUNTER23 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'haf7f0c67} 
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

    #MHPMCOUNTER23 Write value 0xaf7f0c67
    li x3, 0xaf7f0c67
    csrw 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    ##########################
    #MHPMEVENT22 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h11f5c168} 
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

    #MHPMEVENT22 Write value 0x11f5c168
    li x3, 0x11f5c168
    csrw 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    ##########################
    #PMPADDR7 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h61511de4} 
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

    #PMPADDR7 Write value 0x61511de4
    li x3, 0x61511de4
    csrw 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    ##########################
    #MHPMEVENT27 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6c225bc3} 
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

    #MHPMEVENT27 Write value 0x6c225bc3
    li x3, 0x6c225bc3
    csrw 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    ##########################
    #MHPMEVENT25 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7418ffa4} 
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

    #MHPMEVENT25 Write value 0x7418ffa4
    li x3, 0x7418ffa4
    csrw 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    ##########################
    #MHPMCOUNTER3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc7223517} 
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

    #MHPMCOUNTER3 Write value 0xc7223517
    li x3, 0xc7223517
    csrw 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    ##########################
    #MHPMCOUNTERH23 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9c822a60} 
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

    #MHPMCOUNTERH23 Write value 0x9c822a60
    li x3, 0x9c822a60
    csrw 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    ##########################
    #MHPMEVENT3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd3f577ec} 
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

    #MHPMEVENT3 Write value 0xd3f577ec
    li x3, 0xd3f577ec
    csrw 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    ##########################
    #MHPMCOUNTERH5 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he2e18a79} 
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

    #MHPMCOUNTERH5 Write value 0xe2e18a79
    li x3, 0xe2e18a79
    csrw 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    ##########################
    #MHPMCOUNTER21 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5fd876a0} 
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

    #MHPMCOUNTER21 Write value 0x5fd876a0
    li x3, 0x5fd876a0
    csrw 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MIMPID WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTERH13 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7eca517e} 
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

    #MHPMCOUNTERH13 Write value 0x7eca517e
    li x3, 0x7eca517e
    csrw 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    ##########################
    #MHPMEVENT31 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4efe0e63} 
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

    #MHPMEVENT31 Write value 0x4efe0e63
    li x3, 0x4efe0e63
    csrw 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    ##########################
    #MHPMCOUNTER13 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7d43b635} 
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

    #MHPMCOUNTER13 Write value 0x7d43b635
    li x3, 0x7d43b635
    csrw 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    ##########################
    #PMPCFG1 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hf5499765} 
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

    #PMPCFG1 Write value 0xf5499765
    li x3, 0xf5499765
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    ##########################
    #MINSTRET testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdb00149e} 
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

    #MINSTRET Write value 0xdb00149e
    li x3, 0xdb00149e
    csrw 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    ##########################
    #MHPMEVENT26 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha8a0555d} 
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

    #MHPMEVENT26 Write value 0xa8a0555d
    li x3, 0xa8a0555d
    csrw 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    ##########################
    #MHPMCOUNTERH25 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha703c665} 
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

    #MHPMCOUNTERH25 Write value 0xa703c665
    li x3, 0xa703c665
    csrw 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    ##########################
    #MIP testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h1417f03} 
    ##########################
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

    #MIP Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x1417f03
    li x3, 0x1417f03
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #Clear MIP to avoid traping
    csrw 0x344, x0

    #MIP read value
    csrr x14, 0x344

    ##########################
    #MHPMCOUNTERH27 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h22c2d883} 
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

    #MHPMCOUNTERH27 Write value 0x22c2d883
    li x3, 0x22c2d883
    csrw 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    ##########################
    #MHPMCOUNTER5 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'haead10ba} 
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

    #MHPMCOUNTER5 Write value 0xaead10ba
    li x3, 0xaead10ba
    csrw 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    ##########################
    #MHPMCOUNTER22 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha1c3a32b} 
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

    #MHPMCOUNTER22 Write value 0xa1c3a32b
    li x3, 0xa1c3a32b
    csrw 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    ##########################
    #PMPADDR2 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb88d1e05} 
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

    #PMPADDR2 Write value 0xb88d1e05
    li x3, 0xb88d1e05
    csrw 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    ##########################
    #MTVEC testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb550b77c} 
    ##########################
    #MTVEC Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0x0
    li x3, 0x0
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0x55555555
    li x3, 0x55555555
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0xb550b77c
    li x3, 0xb550b77c
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    ##########################
    #MHPMCOUNTER20 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2f4cd91} 
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

    #MHPMCOUNTER20 Write value 0x2f4cd91
    li x3, 0x2f4cd91
    csrw 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    ##########################
    #MHPMCOUNTER17 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hda5f1d92} 
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

    #MHPMCOUNTER17 Write value 0xda5f1d92
    li x3, 0xda5f1d92
    csrw 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    ##########################
    #MHPMEVENT30 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7d2754a6} 
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

    #MHPMEVENT30 Write value 0x7d2754a6
    li x3, 0x7d2754a6
    csrw 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    ##########################
    #MHPMEVENT21 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'heeeafef} 
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

    #MHPMEVENT21 Write value 0xeeeafef
    li x3, 0xeeeafef
    csrw 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    ##########################
    #PMPADDR0 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9053db75} 
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

    #PMPADDR0 Write value 0x9053db75
    li x3, 0x9053db75
    csrw 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #CYCLEH WR skipped since it's a RO register

    #MARCHID WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTERH31 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2e5ba606} 
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

    #MHPMCOUNTERH31 Write value 0x2e5ba606
    li x3, 0x2e5ba606
    csrw 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    ##########################
    #MEPC testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2bc3a8fb} 
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

    #MEPC Write value 0x2bc3a8fb
    li x3, 0x2bc3a8fb
    csrw 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    ##########################
    #MHPMEVENT10 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha2cc9983} 
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

    #MHPMEVENT10 Write value 0xa2cc9983
    li x3, 0xa2cc9983
    csrw 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    ##########################
    #MHPMCOUNTER15 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb9543e0d} 
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

    #MHPMCOUNTER15 Write value 0xb9543e0d
    li x3, 0xb9543e0d
    csrw 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    ##########################
    #MHPMCOUNTER11 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h67f5a962} 
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

    #MHPMCOUNTER11 Write value 0x67f5a962
    li x3, 0x67f5a962
    csrw 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    ##########################
    #MHPMCOUNTERH24 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h759fce08} 
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

    #MHPMCOUNTERH24 Write value 0x759fce08
    li x3, 0x759fce08
    csrw 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    ##########################
    #PMPCFG2 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hf6673a1d} 
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

    #PMPCFG2 Write value 0xf6673a1d
    li x3, 0xf6673a1d
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    ##########################
    #MHPMCOUNTER19 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h99a7fb1e} 
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

    #MHPMCOUNTER19 Write value 0x99a7fb1e
    li x3, 0x99a7fb1e
    csrw 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    ##########################
    #MHPMCOUNTERH8 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha08db110} 
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

    #MHPMCOUNTERH8 Write value 0xa08db110
    li x3, 0xa08db110
    csrw 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    ##########################
    #PMPADDR11 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h255be453} 
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

    #PMPADDR11 Write value 0x255be453
    li x3, 0x255be453
    csrw 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    ##########################
    #MHPMCOUNTER28 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3db87f93} 
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

    #MHPMCOUNTER28 Write value 0x3db87f93
    li x3, 0x3db87f93
    csrw 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    ##########################
    #MHPMCOUNTERH20 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hba919d9a} 
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

    #MHPMCOUNTERH20 Write value 0xba919d9a
    li x3, 0xba919d9a
    csrw 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    ##########################
    #MHPMCOUNTER9 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc2ca733} 
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

    #MHPMCOUNTER9 Write value 0xc2ca733
    li x3, 0xc2ca733
    csrw 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    ##########################
    #MHPMCOUNTER8 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hf8b079c3} 
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

    #MHPMCOUNTER8 Write value 0xf8b079c3
    li x3, 0xf8b079c3
    csrw 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    ##########################
    #MHPMCOUNTERH21 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h15d6d866} 
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

    #MHPMCOUNTERH21 Write value 0x15d6d866
    li x3, 0x15d6d866
    csrw 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    ##########################
    #MHPMCOUNTER29 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb06d5aa8} 
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

    #MHPMCOUNTER29 Write value 0xb06d5aa8
    li x3, 0xb06d5aa8
    csrw 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    ##########################
    #MCYCLE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfc69fd0} 
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

    #MCYCLE Write value 0xfc69fd0
    li x3, 0xfc69fd0
    csrw 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    ##########################
    #MHPMCOUNTER7 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h40a058ab} 
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

    #MHPMCOUNTER7 Write value 0x40a058ab
    li x3, 0x40a058ab
    csrw 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    ##########################
    #MHPMCOUNTERH11 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he5d7e028} 
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

    #MHPMCOUNTERH11 Write value 0xe5d7e028
    li x3, 0xe5d7e028
    csrw 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    ##########################
    #MHPMCOUNTER4 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he3fce265} 
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

    #MHPMCOUNTER4 Write value 0xe3fce265
    li x3, 0xe3fce265
    csrw 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    ##########################
    #MHPMCOUNTER14 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha64668eb} 
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

    #MHPMCOUNTER14 Write value 0xa64668eb
    li x3, 0xa64668eb
    csrw 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    ##########################
    #PMPADDR3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5ec3197f} 
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

    #PMPADDR3 Write value 0x5ec3197f
    li x3, 0x5ec3197f
    csrw 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    ##########################
    #PMPCFG0 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h312c930e} 
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

    #PMPCFG0 Write value 0x312c930e
    li x3, 0x312c930e
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    ##########################
    #MHPMCOUNTERH26 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7881e819} 
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

    #MHPMCOUNTERH26 Write value 0x7881e819
    li x3, 0x7881e819
    csrw 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    ##########################
    #MINSTRETH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'habc1a2af} 
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

    #MINSTRETH Write value 0xabc1a2af
    li x3, 0xabc1a2af
    csrw 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    ##########################
    #MHPMCOUNTERH18 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb276da6d} 
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

    #MHPMCOUNTERH18 Write value 0xb276da6d
    li x3, 0xb276da6d
    csrw 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    ##########################
    #MHPMCOUNTERH16 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcc0d90f2} 
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

    #MHPMCOUNTERH16 Write value 0xcc0d90f2
    li x3, 0xcc0d90f2
    csrw 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    ##########################
    #MHPMEVENT23 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'habfa6455} 
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

    #MHPMEVENT23 Write value 0xabfa6455
    li x3, 0xabfa6455
    csrw 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    ##########################
    #MHPMEVENT11 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h820a9ba9} 
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

    #MHPMEVENT11 Write value 0x820a9ba9
    li x3, 0x820a9ba9
    csrw 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    ##########################
    #MHPMCOUNTERH4 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbeedbfb3} 
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

    #MHPMCOUNTERH4 Write value 0xbeedbfb3
    li x3, 0xbeedbfb3
    csrw 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    ##########################
    #MHPMEVENT28 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd42619d3} 
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

    #MHPMEVENT28 Write value 0xd42619d3
    li x3, 0xd42619d3
    csrw 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    ##########################
    #MHPMEVENT18 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7384ca4d} 
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

    #MHPMEVENT18 Write value 0x7384ca4d
    li x3, 0x7384ca4d
    csrw 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    ##########################
    #MHPMCOUNTER12 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2a363e76} 
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

    #MHPMCOUNTER12 Write value 0x2a363e76
    li x3, 0x2a363e76
    csrw 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    ##########################
    #PMPADDR13 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h71734537} 
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

    #PMPADDR13 Write value 0x71734537
    li x3, 0x71734537
    csrw 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    ##########################
    #MHPMCOUNTER16 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h45ba9ccb} 
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

    #MHPMCOUNTER16 Write value 0x45ba9ccb
    li x3, 0x45ba9ccb
    csrw 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    ##########################
    #MHPMCOUNTERH3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9326b3c7} 
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

    #MHPMCOUNTERH3 Write value 0x9326b3c7
    li x3, 0x9326b3c7
    csrw 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    ##########################
    #MCAUSE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcec490f4} 
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

    #MCAUSE Write value 0xcec490f4
    li x3, 0xcec490f4
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    ##########################
    #MHPMCOUNTER24 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h51e20403} 
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

    #MHPMCOUNTER24 Write value 0x51e20403
    li x3, 0x51e20403
    csrw 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    ##########################
    #MHPMEVENT4 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h47834f6b} 
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

    #MHPMEVENT4 Write value 0x47834f6b
    li x3, 0x47834f6b
    csrw 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    ##########################
    #MISA testing W/R values '{'hfdbf7bfb, 'h2408404, 'h55555555, 'haaaaaaaa, 'heefe0e69} 
    ##########################
    #MISA Write value 0xbfffeef9
    li x3, 0xbfffeef9
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x40001106
    li x3, 0x40001106
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

    #MISA Write value 0xeefe0e69
    li x3, 0xeefe0e69
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    ##########################
    #MHPMCOUNTERH19 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h1f740d78} 
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

    #MHPMCOUNTERH19 Write value 0x1f740d78
    li x3, 0x1f740d78
    csrw 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    ##########################
    #MHPMCOUNTER27 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd04d715b} 
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

    #MHPMCOUNTER27 Write value 0xd04d715b
    li x3, 0xd04d715b
    csrw 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    ##########################
    #MHPMCOUNTER10 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc39dbb5e} 
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

    #MHPMCOUNTER10 Write value 0xc39dbb5e
    li x3, 0xc39dbb5e
    csrw 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    ##########################
    #MHPMEVENT17 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h795a5ef1} 
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

    #MHPMEVENT17 Write value 0x795a5ef1
    li x3, 0x795a5ef1
    csrw 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    ##########################
    #MHPMCOUNTER26 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h1beb6d38} 
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

    #MHPMCOUNTER26 Write value 0x1beb6d38
    li x3, 0x1beb6d38
    csrw 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    ##########################
    #MHPMEVENT24 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he2a4c3bd} 
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

    #MHPMEVENT24 Write value 0xe2a4c3bd
    li x3, 0xe2a4c3bd
    csrw 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    ##########################
    #MHPMCOUNTERH29 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h91d85d53} 
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

    #MHPMCOUNTERH29 Write value 0x91d85d53
    li x3, 0x91d85d53
    csrw 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    ##########################
    #MHPMEVENT15 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4350f67d} 
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

    #MHPMEVENT15 Write value 0x4350f67d
    li x3, 0x4350f67d
    csrw 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    ##########################
    #PMPADDR5 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h8a1ed75a} 
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

    #PMPADDR5 Write value 0x8a1ed75a
    li x3, 0x8a1ed75a
    csrw 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    ##########################
    #MHPMCOUNTER31 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h78abd26e} 
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

    #MHPMCOUNTER31 Write value 0x78abd26e
    li x3, 0x78abd26e
    csrw 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    ##########################
    #MHPMCOUNTERH6 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h82a9239d} 
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

    #MHPMCOUNTERH6 Write value 0x82a9239d
    li x3, 0x82a9239d
    csrw 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    ##########################
    #MHPMCOUNTER6 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h92e8bd5e} 
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

    #MHPMCOUNTER6 Write value 0x92e8bd5e
    li x3, 0x92e8bd5e
    csrw 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    ##########################
    #PMPADDR14 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb8597ede} 
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

    #PMPADDR14 Write value 0xb8597ede
    li x3, 0xb8597ede
    csrw 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    ##########################
    #MHPMCOUNTERH28 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h462244e6} 
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

    #MHPMCOUNTERH28 Write value 0x462244e6
    li x3, 0x462244e6
    csrw 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    ##########################
    #PMPADDR6 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2dbade0b} 
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

    #PMPADDR6 Write value 0x2dbade0b
    li x3, 0x2dbade0b
    csrw 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    ##########################
    #MSTATUS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd64f9b93} 
    ##########################
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

    #MSTATUS Write value 0x55555555
    li x3, 0x55555555
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0xd64f9b93
    li x3, 0xd64f9b93
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    ##########################
    #MHPMEVENT29 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h17cbcca} 
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

    #MHPMEVENT29 Write value 0x17cbcca
    li x3, 0x17cbcca
    csrw 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    ##########################
    #MHPMEVENT7 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd0beeb18} 
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

    #MHPMEVENT7 Write value 0xd0beeb18
    li x3, 0xd0beeb18
    csrw 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    ##########################
    #PMPADDR1 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h84e3551b} 
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

    #PMPADDR1 Write value 0x84e3551b
    li x3, 0x84e3551b
    csrw 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #CYCLE WR skipped since it's a RO register

    ##########################
    #MTVAL testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h162b0d42}
    ##########################
    #MTVAL Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0X343, x3

    #MTVAL read value
    csrr x14, 0X343

    #MTVAL Write value 0x0
    li x3, 0x0
    csrw 0X343, x3

    #MTVAL read value
    csrr x14, 0X343

    #MTVAL Write value 0x55555555
    li x3, 0x55555555
    csrw 0X343, x3

    #MTVAL read value
    csrr x14, 0X343

    #MTVAL Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0X343, x3

    #MTVAL read value
    csrr x14, 0X343

    #MTVAL Write value 0x162b0d42
    li x3, 0x162b0d42
    csrw 0X343, x3

    #MTVAL read value
    csrr x14, 0X343

    ##########################
    #MHPMCOUNTERH10 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h162b0d42} 
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

    #MHPMCOUNTERH10 Write value 0x162b0d42
    li x3, 0x162b0d42
    csrw 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    ##########################
    #MHPMCOUNTERH9 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha567d50c} 
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

    #MHPMCOUNTERH9 Write value 0xa567d50c
    li x3, 0xa567d50c
    csrw 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    ##########################
    #MHPMEVENT19 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbc47526f} 
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

    #MHPMEVENT19 Write value 0xbc47526f
    li x3, 0xbc47526f
    csrw 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    ##########################
    #PMPADDR4 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbc8ec431} 
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

    #PMPADDR4 Write value 0xbc8ec431
    li x3, 0xbc8ec431
    csrw 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    ##########################
    #MHPMEVENT5 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h85c8c92b} 
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

    #MHPMEVENT5 Write value 0x85c8c92b
    li x3, 0x85c8c92b
    csrw 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    ##########################
    #MHPMCOUNTERH22 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h90ba09b5} 
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

    #MHPMCOUNTERH22 Write value 0x90ba09b5
    li x3, 0x90ba09b5
    csrw 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    ##########################
    #MHPMCOUNTERH12 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h61611c4a} 
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

    #MHPMCOUNTERH12 Write value 0x61611c4a
    li x3, 0x61611c4a
    csrw 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    ##########################
    #MHPMEVENT13 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdcfe7bf7} 
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

    #MHPMEVENT13 Write value 0xdcfe7bf7
    li x3, 0xdcfe7bf7
    csrw 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    ##########################
    #MHPMCOUNTERH7 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5d7932b2} 
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

    #MHPMCOUNTERH7 Write value 0x5d7932b2
    li x3, 0x5d7932b2
    csrw 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    ##########################
    #MHPMCOUNTERH15 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h8fcc4c00} 
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

    #MHPMCOUNTERH15 Write value 0x8fcc4c00
    li x3, 0x8fcc4c00
    csrw 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    ##########################
    #PMPCFG3 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb4a7d92c} 
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

    #PMPCFG3 Write value 0xb4a7d92c
    li x3, 0xb4a7d92c
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    ##########################
    #PMPADDR15 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h47df72b4} 
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

    #PMPADDR15 Write value 0x47df72b4
    li x3, 0x47df72b4
    csrw 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    ##########################
    #MHPMCOUNTER18 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h33df2ce6} 
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

    #MHPMCOUNTER18 Write value 0x33df2ce6
    li x3, 0x33df2ce6
    csrw 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    ##########################
    #PMPADDR10 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h166f6452} 
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

    #PMPADDR10 Write value 0x166f6452
    li x3, 0x166f6452
    csrw 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    ##########################
    #MHPMCOUNTERH30 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4a73ebcf} 
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

    #MHPMCOUNTERH30 Write value 0x4a73ebcf
    li x3, 0x4a73ebcf
    csrw 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    ##########################
    #MHPMEVENT14 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfc991421} 
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

    #MHPMEVENT14 Write value 0xfc991421
    li x3, 0xfc991421
    csrw 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    ##########################
    #MHPMCOUNTERH14 testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h9683580} 
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

    #MHPMCOUNTERH14 Write value 0x9683580
    li x3, 0x9683580
    csrw 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    ret
