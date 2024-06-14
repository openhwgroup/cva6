# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

csrrst:
    #Start CSR tests: Read all registers reset value in random order
    #User ignored registers: 

    #MCAUSE read value
    csrr x14, 0x342

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MISA read value
    csrr x14, 0x301

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPADDR14 read value
    csrr x14, 0x3be

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MIP read value
    csrr x14, 0x344

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MTVEC read value
    csrr x14, 0x305

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MCYCLEH read value
    csrr x14, 0xb80

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MIE read value
    csrr x14, 0x304

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MTVAL read value
    csrr x14, 0x343

    #MCYCLE read value
    csrr x14, 0xb00

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #MSTATUS read value
    csrr x14, 0x300

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MARCHID read value
    csrr x14, 0xf12

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MINSTRETH read value
    csrr x14, 0xb82

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MINSTRET read value
    csrr x14, 0xb02

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MIMPID read value
    csrr x14, 0xf13

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHARTID read value
    csrr x14, 0xf14

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #MSCRATCH read value
    csrr x14, 0x340

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MEPC read value
    csrr x14, 0x341

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MSTATUSH read value
    csrr x14, 0x310

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #ICACHE read value
    csrr x14, 0x7c0

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MVENDORID read value
    csrr x14, 0xf11

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    ret
