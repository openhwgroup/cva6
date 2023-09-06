# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

csrcsi:
    #Start CSR tests: Write/Read all registers using Clear/Set immediate instructions
    #User ignored registers: MHPMEVENT3 ,MHPMEVENT4 ,MHPMEVENT5 ,MHPMEVENT6 ,MHPMEVENT7 ,MHPMEVENT8 ,MHPMEVENT9 ,MHPMEVENT10 ,MHPMEVENT11 ,MHPMEVENT12 ,MHPMEVENT13 ,MHPMEVENT14 ,MHPMEVENT15 ,MHPMEVENT16 ,MHPMEVENT17 ,MHPMEVENT18 ,MHPMEVENT19 ,MHPMEVENT20 ,MHPMEVENT21 ,MHPMEVENT22 ,MHPMEVENT23 ,MHPMEVENT24 ,MHPMEVENT25 ,MHPMEVENT26 ,MHPMEVENT27 ,MHPMEVENT28 ,MHPMEVENT29 ,MHPMEVENT30 ,MHPMEVENT31 ,PMPCFG0 ,PMPCFG1 ,PMPCFG2 ,PMPCFG3 ,PMPADDR0 ,PMPADDR1 ,PMPADDR2 ,PMPADDR3 ,PMPADDR4 ,PMPADDR5 ,PMPADDR6 ,PMPADDR7 ,PMPADDR8 ,PMPADDR9 ,PMPADDR10 ,PMPADDR11 ,PMPADDR12 ,PMPADDR13 ,PMPADDR14 ,PMPADDR15 ,ICACHE ,MHPMCOUNTER3 ,MHPMCOUNTER4 ,MHPMCOUNTER5 ,MHPMCOUNTER6 ,MHPMCOUNTER7 ,MHPMCOUNTER8 ,MHPMCOUNTER9 ,MHPMCOUNTER10 ,MHPMCOUNTER11 ,MHPMCOUNTER12 ,MHPMCOUNTER13 ,MHPMCOUNTER14 ,MHPMCOUNTER15 ,MHPMCOUNTER16 ,MHPMCOUNTER17 ,MHPMCOUNTER18 ,MHPMCOUNTER19 ,MHPMCOUNTER20 ,MHPMCOUNTER21 ,MHPMCOUNTER22 ,MHPMCOUNTER23 ,MHPMCOUNTER24 ,MHPMCOUNTER25 ,MHPMCOUNTER26 ,MHPMCOUNTER27 ,MHPMCOUNTER28 ,MHPMCOUNTER29 ,MHPMCOUNTER30 ,MHPMCOUNTER31 ,MHPMCOUNTERH3 ,MHPMCOUNTERH4 ,MHPMCOUNTERH5 ,MHPMCOUNTERH6 ,MHPMCOUNTERH7 ,MHPMCOUNTERH8 ,MHPMCOUNTERH9 ,MHPMCOUNTERH10 ,MHPMCOUNTERH11 ,MHPMCOUNTERH12 ,MHPMCOUNTERH13 ,MHPMCOUNTERH14 ,MHPMCOUNTERH15 ,MHPMCOUNTERH16 ,MHPMCOUNTERH17 ,MHPMCOUNTERH18 ,MHPMCOUNTERH19 ,MHPMCOUNTERH20 ,MHPMCOUNTERH21 ,MHPMCOUNTERH22 ,MHPMCOUNTERH23 ,MHPMCOUNTERH24 ,MHPMCOUNTERH25 ,MHPMCOUNTERH26 ,MHPMCOUNTERH27 ,MHPMCOUNTERH28 ,MHPMCOUNTERH29 ,MHPMCOUNTERH30 ,MHPMCOUNTERH31 ,
    ##########################
    #MSTATUS testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16}
    ##########################
    #MSTATUS Write clear/set value 0x1f
    csrrci x14, 0x300, 0x0
    csrrsi x14, 0x300, 0x1f

    #MSTATUS read value, expected 0xa
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x0
    csrrci x14, 0x300, 0x1f
    csrrsi x14, 0x300, 0x0

    #MSTATUS read value, expected 0x0
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x15
    csrrci x14, 0x300, 0xa
    csrrsi x14, 0x300, 0x15

    #MSTATUS read value, expected 0x0
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0xa
    csrrci x14, 0x300, 0x15
    csrrsi x14, 0x300, 0xa

    #MSTATUS read value, expected 0xa
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x16
    csrrci x14, 0x300, 0x9
    csrrsi x14, 0x300, 0x16

    #MSTATUS read value, expected 0x2
    csrr x14, 0x300

    ##########################
    #MTVAL testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18}
    ##########################
    #MTVAL Write clear/set value 0x1f
    csrrci x14, 0x343, 0x0
    csrrsi x14, 0x343, 0x1f

    #MTVAL read value, expected 0x1f
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x0
    csrrci x14, 0x343, 0x1f
    csrrsi x14, 0x343, 0x0

    #MTVAL read value, expected 0x0
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x15
    csrrci x14, 0x343, 0xa
    csrrsi x14, 0x343, 0x15

    #MTVAL read value, expected 0x15
    csrr x14, 0x343

    #MTVAL Write clear/set value 0xa
    csrrci x14, 0x343, 0x15
    csrrsi x14, 0x343, 0xa

    #MTVAL read value, expected 0xa
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x18
    csrrci x14, 0x343, 0x7
    csrrsi x14, 0x343, 0x18

    #MTVAL read value, expected 0x18
    csrr x14, 0x343

    ##########################
    #MSCRATCH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h9}
    ##########################
    #MSCRATCH Write clear/set value 0x1f
    csrrci x14, 0x340, 0x0
    csrrsi x14, 0x340, 0x1f

    #MSCRATCH read value, expected 0x1f
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x0
    csrrci x14, 0x340, 0x1f
    csrrsi x14, 0x340, 0x0

    #MSCRATCH read value, expected 0x0
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x15
    csrrci x14, 0x340, 0xa
    csrrsi x14, 0x340, 0x15

    #MSCRATCH read value, expected 0x15
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0xa
    csrrci x14, 0x340, 0x15
    csrrsi x14, 0x340, 0xa

    #MSCRATCH read value, expected 0xa
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x9
    csrrci x14, 0x340, 0x16
    csrrsi x14, 0x340, 0x9

    #MSCRATCH read value, expected 0x9
    csrr x14, 0x340

    ##########################
    #MCYCLE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2}
    ##########################
    #MCYCLE Write clear/set value 0x1f
    csrrci x14, 0xb00, 0x0
    csrrsi x14, 0xb00, 0x1f

    #MCYCLE read value, expected 0x1f
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x0
    csrrci x14, 0xb00, 0x1f
    csrrsi x14, 0xb00, 0x0

    #MCYCLE read value, expected 0x0
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x15
    csrrci x14, 0xb00, 0xa
    csrrsi x14, 0xb00, 0x15

    #MCYCLE read value, expected 0x15
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0xa
    csrrci x14, 0xb00, 0x15
    csrrsi x14, 0xb00, 0xa

    #MCYCLE read value, expected 0xa
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x2
    csrrci x14, 0xb00, 0x1d
    csrrsi x14, 0xb00, 0x2

    #MCYCLE read value, expected 0x2
    csrr x14, 0xb00

    ##########################
    #MTVEC testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7}
    ##########################
    #MTVEC Write clear/set value 0x1f
    csrrci x14, 0x305, 0x0
    csrrsi x14, 0x305, 0x1f

    #MTVEC read value, expected 0x1f
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x0
    csrrci x14, 0x305, 0x1f
    csrrsi x14, 0x305, 0x0

    #MTVEC read value, expected 0x0
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x15
    csrrci x14, 0x305, 0xa
    csrrsi x14, 0x305, 0x15

    #MTVEC read value, expected 0x15
    csrr x14, 0x305

    #MTVEC Write clear/set value 0xa
    csrrci x14, 0x305, 0x15
    csrrsi x14, 0x305, 0xa

    #MTVEC read value, expected 0xa
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x7
    csrrci x14, 0x305, 0x18
    csrrsi x14, 0x305, 0x7

    #MTVEC read value, expected 0x7
    csrr x14, 0x305

    ##########################
    #MCAUSE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16}
    ##########################
    #MCAUSE Write clear/set value 0x1f
    csrrci x14, 0x342, 0x0
    csrrsi x14, 0x342, 0x1f

    #MCAUSE read value, expected 0x1f
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x0
    csrrci x14, 0x342, 0x1f
    csrrsi x14, 0x342, 0x0

    #MCAUSE read value, expected 0x0
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x15
    csrrci x14, 0x342, 0xa
    csrrsi x14, 0x342, 0x15

    #MCAUSE read value, expected 0x15
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0xa
    csrrci x14, 0x342, 0x15
    csrrsi x14, 0x342, 0xa

    #MCAUSE read value, expected 0xa
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x16
    csrrci x14, 0x342, 0x9
    csrrsi x14, 0x342, 0x16

    #MCAUSE read value, expected 0x16
    csrr x14, 0x342

    ##########################
    #MINSTRETH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f}
    ##########################
    #MINSTRETH Write clear/set value 0x1f
    csrrci x14, 0xb82, 0x0
    csrrsi x14, 0xb82, 0x1f

    #MINSTRETH read value, expected 0x1f
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x0
    csrrci x14, 0xb82, 0x1f
    csrrsi x14, 0xb82, 0x0

    #MINSTRETH read value, expected 0x0
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x15
    csrrci x14, 0xb82, 0xa
    csrrsi x14, 0xb82, 0x15

    #MINSTRETH read value, expected 0x15
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0xa
    csrrci x14, 0xb82, 0x15
    csrrsi x14, 0xb82, 0xa

    #MINSTRETH read value, expected 0xa
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x1f
    csrrci x14, 0xb82, 0x0
    csrrsi x14, 0xb82, 0x1f

    #MINSTRETH read value, expected 0x1f
    csrr x14, 0xb82

    ##########################
    #MIP testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10}
    ##########################
    #MIP Write clear/set value 0x1f
    csrrci x14, 0x344, 0x0
    csrrsi x14, 0x344, 0x1f

    #MIP read value, expected 0x1b
    csrr x14, 0x344

    #MIP Write clear/set value 0x0
    csrrci x14, 0x344, 0x17
    csrrsi x14, 0x344, 0x0

    #MIP read value, expected 0x0
    csrr x14, 0x344

    #MIP Write clear/set value 0x15
    csrrci x14, 0x344, 0x2
    csrrsi x14, 0x344, 0x15

    #MIP read value, expected 0x11
    csrr x14, 0x344

    #MIP Write clear/set value 0xa
    csrrci x14, 0x344, 0x15
    csrrsi x14, 0x344, 0xa

    #MIP read value, expected 0xa
    csrr x14, 0x344

    #MIP Write clear/set value 0x10
    csrrci x14, 0x344, 0x7
    csrrsi x14, 0x344, 0x10

    #MIP read value, expected 0x10
    csrr x14, 0x344

    ##########################
    #MISA testing W/R values '{'h1b, 'h4, 'h15, 'ha, 'h3}
    ##########################
    #MISA Write clear/set value 0x1b
    csrrci x14, 0x301, 0x4
    csrrsi x14, 0x301, 0x1b

    #MISA read value, expected 0x1b
    csrr x14, 0x301

    #MISA Write clear/set value 0x4
    csrrci x14, 0x301, 0x1b
    csrrsi x14, 0x301, 0x4

    #MISA read value, expected 0x4
    csrr x14, 0x301

    #MISA Write clear/set value 0x15
    csrrci x14, 0x301, 0xa
    csrrsi x14, 0x301, 0x15

    #MISA read value, expected 0x15
    csrr x14, 0x301

    #MISA Write clear/set value 0xa
    csrrci x14, 0x301, 0x15
    csrrsi x14, 0x301, 0xa

    #MISA read value, expected 0xa
    csrr x14, 0x301

    #MISA Write clear/set value 0x3
    csrrci x14, 0x301, 0x1c
    csrrsi x14, 0x301, 0x3

    #MISA read value, expected 0x3
    csrr x14, 0x301

    ##########################
    #MSTATUSH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2}
    ##########################
    #MSTATUSH Write clear/set value 0x1f
    csrrci x14, 0x310, 0x0
    csrrsi x14, 0x310, 0x1f

    #MSTATUSH read value, expected 0x10
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x0
    csrrci x14, 0x310, 0x1f
    csrrsi x14, 0x310, 0x0

    #MSTATUSH read value, expected 0x0
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x15
    csrrci x14, 0x310, 0xa
    csrrsi x14, 0x310, 0x15

    #MSTATUSH read value, expected 0x10
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0xa
    csrrci x14, 0x310, 0x15
    csrrsi x14, 0x310, 0xa

    #MSTATUSH read value, expected 0x0
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x2
    csrrci x14, 0x310, 0x1d
    csrrsi x14, 0x310, 0x2

    #MSTATUSH read value, expected 0x0
    csrr x14, 0x310

    ##########################
    #MCYCLEH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd}
    ##########################
    #MCYCLEH Write clear/set value 0x1f
    csrrci x14, 0xb80, 0x0
    csrrsi x14, 0xb80, 0x1f

    #MCYCLEH read value, expected 0x1f
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x0
    csrrci x14, 0xb80, 0x1f
    csrrsi x14, 0xb80, 0x0

    #MCYCLEH read value, expected 0x0
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x15
    csrrci x14, 0xb80, 0xa
    csrrsi x14, 0xb80, 0x15

    #MCYCLEH read value, expected 0x15
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0xa
    csrrci x14, 0xb80, 0x15
    csrrsi x14, 0xb80, 0xa

    #MCYCLEH read value, expected 0xa
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0xd
    csrrci x14, 0xb80, 0x12
    csrrsi x14, 0xb80, 0xd

    #MCYCLEH read value, expected 0xd
    csrr x14, 0xb80

    ##########################
    #MIE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h6}
    ##########################
    #MIE Write clear/set value 0x1f
    csrrci x14, 0x304, 0x0
    csrrsi x14, 0x304, 0x1f

    #MIE read value, expected 0x1b
    csrr x14, 0x304

    #MIE Write clear/set value 0x0
    csrrci x14, 0x304, 0x1f
    csrrsi x14, 0x304, 0x0

    #MIE read value, expected 0x0
    csrr x14, 0x304

    #MIE Write clear/set value 0x15
    csrrci x14, 0x304, 0xa
    csrrsi x14, 0x304, 0x15

    #MIE read value, expected 0x11
    csrr x14, 0x304

    #MIE Write clear/set value 0xa
    csrrci x14, 0x304, 0x15
    csrrsi x14, 0x304, 0xa

    #MIE read value, expected 0xa
    csrr x14, 0x304

    #MIE Write clear/set value 0x6
    csrrci x14, 0x304, 0x19
    csrrsi x14, 0x304, 0x6

    #MIE read value, expected 0x2
    csrr x14, 0x304

    ##########################
    #MEPC testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1c}
    ##########################
    #MEPC Write clear/set value 0x1f
    csrrci x14, 0x341, 0x0
    csrrsi x14, 0x341, 0x1f

    #MEPC read value, expected 0x1f
    csrr x14, 0x341

    #MEPC Write clear/set value 0x0
    csrrci x14, 0x341, 0x1f
    csrrsi x14, 0x341, 0x0

    #MEPC read value, expected 0x0
    csrr x14, 0x341

    #MEPC Write clear/set value 0x15
    csrrci x14, 0x341, 0xa
    csrrsi x14, 0x341, 0x15

    #MEPC read value, expected 0x15
    csrr x14, 0x341

    #MEPC Write clear/set value 0xa
    csrrci x14, 0x341, 0x15
    csrrsi x14, 0x341, 0xa

    #MEPC read value, expected 0xa
    csrr x14, 0x341

    #MEPC Write clear/set value 0x1c
    csrrci x14, 0x341, 0x3
    csrrsi x14, 0x341, 0x1c

    #MEPC read value, expected 0x1c
    csrr x14, 0x341

    ##########################
    #MINSTRET testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1}
    ##########################
    #MINSTRET Write clear/set value 0x1f
    csrrci x14, 0xb02, 0x0
    csrrsi x14, 0xb02, 0x1f

    #MINSTRET read value, expected 0x1f
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x0
    csrrci x14, 0xb02, 0x1f
    csrrsi x14, 0xb02, 0x0

    #MINSTRET read value, expected 0x0
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x15
    csrrci x14, 0xb02, 0xa
    csrrsi x14, 0xb02, 0x15

    #MINSTRET read value, expected 0x15
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0xa
    csrrci x14, 0xb02, 0x15
    csrrsi x14, 0xb02, 0xa

    #MINSTRET read value, expected 0xa
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x1
    csrrci x14, 0xb02, 0x1e
    csrrsi x14, 0xb02, 0x1

    #MINSTRET read value, expected 0x1
    csrr x14, 0xb02

    ret
