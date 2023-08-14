# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

csrcs:
    #Start CSR tests: Write/Read all registers using Clear/Set instructions
    #User ignored registers: MHPMEVENT3 ,MHPMEVENT4 ,MHPMEVENT5 ,MHPMEVENT6 ,MHPMEVENT7 ,MHPMEVENT8 ,MHPMEVENT9 ,MHPMEVENT10 ,MHPMEVENT11 ,MHPMEVENT12 ,MHPMEVENT13 ,MHPMEVENT14 ,MHPMEVENT15 ,MHPMEVENT16 ,MHPMEVENT17 ,MHPMEVENT18 ,MHPMEVENT19 ,MHPMEVENT20 ,MHPMEVENT21 ,MHPMEVENT22 ,MHPMEVENT23 ,MHPMEVENT24 ,MHPMEVENT25 ,MHPMEVENT26 ,MHPMEVENT27 ,MHPMEVENT28 ,MHPMEVENT29 ,MHPMEVENT30 ,MHPMEVENT31 ,PMPCFG0 ,PMPCFG1 ,PMPCFG2 ,PMPCFG3 ,PMPADDR0 ,PMPADDR1 ,PMPADDR2 ,PMPADDR3 ,PMPADDR4 ,PMPADDR5 ,PMPADDR6 ,PMPADDR7 ,PMPADDR8 ,PMPADDR9 ,PMPADDR10 ,PMPADDR11 ,PMPADDR12 ,PMPADDR13 ,PMPADDR14 ,PMPADDR15 ,ICACHE ,MHPMCOUNTER3 ,MHPMCOUNTER4 ,MHPMCOUNTER5 ,MHPMCOUNTER6 ,MHPMCOUNTER7 ,MHPMCOUNTER8 ,MHPMCOUNTER9 ,MHPMCOUNTER10 ,MHPMCOUNTER11 ,MHPMCOUNTER12 ,MHPMCOUNTER13 ,MHPMCOUNTER14 ,MHPMCOUNTER15 ,MHPMCOUNTER16 ,MHPMCOUNTER17 ,MHPMCOUNTER18 ,MHPMCOUNTER19 ,MHPMCOUNTER20 ,MHPMCOUNTER21 ,MHPMCOUNTER22 ,MHPMCOUNTER23 ,MHPMCOUNTER24 ,MHPMCOUNTER25 ,MHPMCOUNTER26 ,MHPMCOUNTER27 ,MHPMCOUNTER28 ,MHPMCOUNTER29 ,MHPMCOUNTER30 ,MHPMCOUNTER31 ,MHPMCOUNTERH3 ,MHPMCOUNTERH4 ,MHPMCOUNTERH5 ,MHPMCOUNTERH6 ,MHPMCOUNTERH7 ,MHPMCOUNTERH8 ,MHPMCOUNTERH9 ,MHPMCOUNTERH10 ,MHPMCOUNTERH11 ,MHPMCOUNTERH12 ,MHPMCOUNTERH13 ,MHPMCOUNTERH14 ,MHPMCOUNTERH15 ,MHPMCOUNTERH16 ,MHPMCOUNTERH17 ,MHPMCOUNTERH18 ,MHPMCOUNTERH19 ,MHPMCOUNTERH20 ,MHPMCOUNTERH21 ,MHPMCOUNTERH22 ,MHPMCOUNTERH23 ,MHPMCOUNTERH24 ,MHPMCOUNTERH25 ,MHPMCOUNTERH26 ,MHPMCOUNTERH27 ,MHPMCOUNTERH28 ,MHPMCOUNTERH29 ,MHPMCOUNTERH30 ,MHPMCOUNTERH31 ,
    ##########################
    #MSTATUS testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18}
    ##########################
    #MSTATUS Write clear/set value 0x1f
    li x3, 0x7ffe19e0
    csrrc x14, 0x300, x3
    li x3, 0x1f
    csrrs x14, 0x300, x3

    #MSTATUS read value, expected 0xa
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x0
    li x3, 0x7ffe19ff
    csrrc x14, 0x300, x3
    li x3, 0x0
    csrrs x14, 0x300, x3

    #MSTATUS read value, expected 0x0
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x15
    li x3, 0x7ffe19ea
    csrrc x14, 0x300, x3
    li x3, 0x15
    csrrs x14, 0x300, x3

    #MSTATUS read value, expected 0x0
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0xa
    li x3, 0x7ffe19f5
    csrrc x14, 0x300, x3
    li x3, 0xa
    csrrs x14, 0x300, x3

    #MSTATUS read value, expected 0xa
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x18
    li x3, 0x7ffe19e7
    csrrc x14, 0x300, x3
    li x3, 0x18
    csrrs x14, 0x300, x3

    #MSTATUS read value, expected 0x8
    csrr x14, 0x300

    ##########################
    #MTVEC testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4}
    ##########################
    #MTVEC Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x305, x3
    li x3, 0x1f
    csrrs x14, 0x305, x3

    #MTVEC read value, expected 0x1f
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x305, x3
    li x3, 0x0
    csrrs x14, 0x305, x3

    #MTVEC read value, expected 0x0
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x305, x3
    li x3, 0x15
    csrrs x14, 0x305, x3

    #MTVEC read value, expected 0x15
    csrr x14, 0x305

    #MTVEC Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x305, x3
    li x3, 0xa
    csrrs x14, 0x305, x3

    #MTVEC read value, expected 0xa
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x4
    li x3, 0xfffffffb
    csrrc x14, 0x305, x3
    li x3, 0x4
    csrrs x14, 0x305, x3

    #MTVEC read value, expected 0x4
    csrr x14, 0x305

    ##########################
    #MSTATUSH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1}
    ##########################
    #MSTATUSH Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x310, x3
    li x3, 0x1f
    csrrs x14, 0x310, x3

    #MSTATUSH read value, expected 0x10
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x310, x3
    li x3, 0x0
    csrrs x14, 0x310, x3

    #MSTATUSH read value, expected 0x0
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x310, x3
    li x3, 0x15
    csrrs x14, 0x310, x3

    #MSTATUSH read value, expected 0x10
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x310, x3
    li x3, 0xa
    csrrs x14, 0x310, x3

    #MSTATUSH read value, expected 0x0
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x1
    li x3, 0xfffffffe
    csrrc x14, 0x310, x3
    li x3, 0x1
    csrrs x14, 0x310, x3

    #MSTATUSH read value, expected 0x0
    csrr x14, 0x310

    ##########################
    #MCYCLEH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2}
    ##########################
    #MCYCLEH Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb80, x3
    li x3, 0x1f
    csrrs x14, 0xb80, x3

    #MCYCLEH read value, expected 0x1f
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb80, x3
    li x3, 0x0
    csrrs x14, 0xb80, x3

    #MCYCLEH read value, expected 0x0
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb80, x3
    li x3, 0x15
    csrrs x14, 0xb80, x3

    #MCYCLEH read value, expected 0x15
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb80, x3
    li x3, 0xa
    csrrs x14, 0xb80, x3

    #MCYCLEH read value, expected 0xa
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x2
    li x3, 0xfffffffd
    csrrc x14, 0xb80, x3
    li x3, 0x2
    csrrs x14, 0xb80, x3

    #MCYCLEH read value, expected 0x2
    csrr x14, 0xb80

    ##########################
    #MSCRATCH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd}
    ##########################
    #MSCRATCH Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x340, x3
    li x3, 0x1f
    csrrs x14, 0x340, x3

    #MSCRATCH read value, expected 0x1f
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x340, x3
    li x3, 0x0
    csrrs x14, 0x340, x3

    #MSCRATCH read value, expected 0x0
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x340, x3
    li x3, 0x15
    csrrs x14, 0x340, x3

    #MSCRATCH read value, expected 0x15
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x340, x3
    li x3, 0xa
    csrrs x14, 0x340, x3

    #MSCRATCH read value, expected 0xa
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0xd
    li x3, 0xfffffff2
    csrrc x14, 0x340, x3
    li x3, 0xd
    csrrs x14, 0x340, x3

    #MSCRATCH read value, expected 0xd
    csrr x14, 0x340

    ##########################
    #MINSTRET testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h15}
    ##########################
    #MINSTRET Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb02, x3
    li x3, 0x1f
    csrrs x14, 0xb02, x3

    #MINSTRET read value, expected 0x1f
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb02, x3
    li x3, 0x0
    csrrs x14, 0xb02, x3

    #MINSTRET read value, expected 0x0
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb02, x3
    li x3, 0x15
    csrrs x14, 0xb02, x3

    #MINSTRET read value, expected 0x15
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb02, x3
    li x3, 0xa
    csrrs x14, 0xb02, x3

    #MINSTRET read value, expected 0xa
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb02, x3
    li x3, 0x15
    csrrs x14, 0xb02, x3

    #MINSTRET read value, expected 0x15
    csrr x14, 0xb02

    ##########################
    #MIP testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4}
    ##########################
    #MIP Write clear/set value 0x1f
    li x3, 0xfffff760
    csrrc x14, 0x344, x3
    li x3, 0x1f
    csrrs x14, 0x344, x3

    #MIP read value, expected 0x1b
    csrr x14, 0x344

    #MIP Write clear/set value 0x0
    li x3, 0xfffff777
    csrrc x14, 0x344, x3
    li x3, 0x0
    csrrs x14, 0x344, x3

    #MIP read value, expected 0x0
    csrr x14, 0x344

    #MIP Write clear/set value 0x15
    li x3, 0xfffff762
    csrrc x14, 0x344, x3
    li x3, 0x15
    csrrs x14, 0x344, x3

    #MIP read value, expected 0x11
    csrr x14, 0x344

    #MIP Write clear/set value 0xa
    li x3, 0xfffff775
    csrrc x14, 0x344, x3
    li x3, 0xa
    csrrs x14, 0x344, x3

    #MIP read value, expected 0xa
    csrr x14, 0x344

    #MIP Write clear/set value 0x4
    li x3, 0xfffff773
    csrrc x14, 0x344, x3
    li x3, 0x4
    csrrs x14, 0x344, x3

    #MIP read value, expected 0x0
    csrr x14, 0x344

    ##########################
    #MEPC testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1b}
    ##########################
    #MEPC Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x341, x3
    li x3, 0x1f
    csrrs x14, 0x341, x3

    #MEPC read value, expected 0x1f
    csrr x14, 0x341

    #MEPC Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x341, x3
    li x3, 0x0
    csrrs x14, 0x341, x3

    #MEPC read value, expected 0x0
    csrr x14, 0x341

    #MEPC Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x341, x3
    li x3, 0x15
    csrrs x14, 0x341, x3

    #MEPC read value, expected 0x15
    csrr x14, 0x341

    #MEPC Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x341, x3
    li x3, 0xa
    csrrs x14, 0x341, x3

    #MEPC read value, expected 0xa
    csrr x14, 0x341

    #MEPC Write clear/set value 0x1b
    li x3, 0xffffffe4
    csrrc x14, 0x341, x3
    li x3, 0x1b
    csrrs x14, 0x341, x3

    #MEPC read value, expected 0x1b
    csrr x14, 0x341

    ##########################
    #MCYCLE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1d}
    ##########################
    #MCYCLE Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb00, x3
    li x3, 0x1f
    csrrs x14, 0xb00, x3

    #MCYCLE read value, expected 0x1f
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb00, x3
    li x3, 0x0
    csrrs x14, 0xb00, x3

    #MCYCLE read value, expected 0x0
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb00, x3
    li x3, 0x15
    csrrs x14, 0xb00, x3

    #MCYCLE read value, expected 0x15
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb00, x3
    li x3, 0xa
    csrrs x14, 0xb00, x3

    #MCYCLE read value, expected 0xa
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x1d
    li x3, 0xffffffe2
    csrrc x14, 0xb00, x3
    li x3, 0x1d
    csrrs x14, 0xb00, x3

    #MCYCLE read value, expected 0x1d
    csrr x14, 0xb00

    ##########################
    #MINSTRETH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a}
    ##########################
    #MINSTRETH Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb82, x3
    li x3, 0x1f
    csrrs x14, 0xb82, x3

    #MINSTRETH read value, expected 0x1f
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb82, x3
    li x3, 0x0
    csrrs x14, 0xb82, x3

    #MINSTRETH read value, expected 0x0
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb82, x3
    li x3, 0x15
    csrrs x14, 0xb82, x3

    #MINSTRETH read value, expected 0x15
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb82, x3
    li x3, 0xa
    csrrs x14, 0xb82, x3

    #MINSTRETH read value, expected 0xa
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x1a
    li x3, 0xffffffe5
    csrrc x14, 0xb82, x3
    li x3, 0x1a
    csrrs x14, 0xb82, x3

    #MINSTRETH read value, expected 0x1a
    csrr x14, 0xb82

    ##########################
    #MCAUSE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16}
    ##########################
    #MCAUSE Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x342, x3
    li x3, 0x1f
    csrrs x14, 0x342, x3

    #MCAUSE read value, expected 0x1f
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x342, x3
    li x3, 0x0
    csrrs x14, 0x342, x3

    #MCAUSE read value, expected 0x0
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x342, x3
    li x3, 0x15
    csrrs x14, 0x342, x3

    #MCAUSE read value, expected 0x15
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x342, x3
    li x3, 0xa
    csrrs x14, 0x342, x3

    #MCAUSE read value, expected 0xa
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x16
    li x3, 0xffffffe9
    csrrc x14, 0x342, x3
    li x3, 0x16
    csrrs x14, 0x342, x3

    #MCAUSE read value, expected 0x16
    csrr x14, 0x342

    ##########################
    #MISA testing W/R values '{'h1b, 'h4, 'h15, 'ha, 'h8}
    ##########################
    #MISA Write clear/set value 0x1b
    li x3, 0xffffffe4
    csrrc x14, 0x301, x3
    li x3, 0x1b
    csrrs x14, 0x301, x3

    #MISA read value, expected 0x1b
    csrr x14, 0x301

    #MISA Write clear/set value 0x4
    li x3, 0xfffffffb
    csrrc x14, 0x301, x3
    li x3, 0x4
    csrrs x14, 0x301, x3

    #MISA read value, expected 0x4
    csrr x14, 0x301

    #MISA Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x301, x3
    li x3, 0x15
    csrrs x14, 0x301, x3

    #MISA read value, expected 0x15
    csrr x14, 0x301

    #MISA Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x301, x3
    li x3, 0xa
    csrrs x14, 0x301, x3

    #MISA read value, expected 0xa
    csrr x14, 0x301

    #MISA Write clear/set value 0x8
    li x3, 0xfffffff7
    csrrc x14, 0x301, x3
    li x3, 0x8
    csrrs x14, 0x301, x3

    #MISA read value, expected 0x8
    csrr x14, 0x301

    ##########################
    #MTVAL testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1e}
    ##########################
    #MTVAL Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x343, x3
    li x3, 0x1f
    csrrs x14, 0x343, x3

    #MTVAL read value, expected 0x1f
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x343, x3
    li x3, 0x0
    csrrs x14, 0x343, x3

    #MTVAL read value, expected 0x0
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x343, x3
    li x3, 0x15
    csrrs x14, 0x343, x3

    #MTVAL read value, expected 0x15
    csrr x14, 0x343

    #MTVAL Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x343, x3
    li x3, 0xa
    csrrs x14, 0x343, x3

    #MTVAL read value, expected 0xa
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x1e
    li x3, 0xffffffe1
    csrrc x14, 0x343, x3
    li x3, 0x1e
    csrrs x14, 0x343, x3

    #MTVAL read value, expected 0x1e
    csrr x14, 0x343

    ##########################
    #MIE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a}
    ##########################
    #MIE Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x304, x3
    li x3, 0x1f
    csrrs x14, 0x304, x3

    #MIE read value, expected 0x1b
    csrr x14, 0x304

    #MIE Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x304, x3
    li x3, 0x0
    csrrs x14, 0x304, x3

    #MIE read value, expected 0x0
    csrr x14, 0x304

    #MIE Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x304, x3
    li x3, 0x15
    csrrs x14, 0x304, x3

    #MIE read value, expected 0x11
    csrr x14, 0x304

    #MIE Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x304, x3
    li x3, 0xa
    csrrs x14, 0x304, x3

    #MIE read value, expected 0xa
    csrr x14, 0x304

    #MIE Write clear/set value 0x1a
    li x3, 0xffffffe5
    csrrc x14, 0x304, x3
    li x3, 0x1a
    csrrs x14, 0x304, x3

    #MIE read value, expected 0x1a
    csrr x14, 0x304

    ret
