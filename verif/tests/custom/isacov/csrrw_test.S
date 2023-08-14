# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

csrrw:
    #Start CSR tests: Write/Read all registers
    #User ignored registers: MHPMEVENT3 ,MHPMEVENT4 ,MHPMEVENT5 ,MHPMEVENT6 ,MHPMEVENT7 ,MHPMEVENT8 ,MHPMEVENT9 ,MHPMEVENT10 ,MHPMEVENT11 ,MHPMEVENT12 ,MHPMEVENT13 ,MHPMEVENT14 ,MHPMEVENT15 ,MHPMEVENT16 ,MHPMEVENT17 ,MHPMEVENT18 ,MHPMEVENT19 ,MHPMEVENT20 ,MHPMEVENT21 ,MHPMEVENT22 ,MHPMEVENT23 ,MHPMEVENT24 ,MHPMEVENT25 ,MHPMEVENT26 ,MHPMEVENT27 ,MHPMEVENT28 ,MHPMEVENT29 ,MHPMEVENT30 ,MHPMEVENT31 ,PMPCFG0 ,PMPCFG1 ,PMPCFG2 ,PMPCFG3 ,PMPADDR0 ,PMPADDR1 ,PMPADDR2 ,PMPADDR3 ,PMPADDR4 ,PMPADDR5 ,PMPADDR6 ,PMPADDR7 ,PMPADDR8 ,PMPADDR9 ,PMPADDR10 ,PMPADDR11 ,PMPADDR12 ,PMPADDR13 ,PMPADDR14 ,PMPADDR15 ,ICACHE ,MHPMCOUNTER3 ,MHPMCOUNTER4 ,MHPMCOUNTER5 ,MHPMCOUNTER6 ,MHPMCOUNTER7 ,MHPMCOUNTER8 ,MHPMCOUNTER9 ,MHPMCOUNTER10 ,MHPMCOUNTER11 ,MHPMCOUNTER12 ,MHPMCOUNTER13 ,MHPMCOUNTER14 ,MHPMCOUNTER15 ,MHPMCOUNTER16 ,MHPMCOUNTER17 ,MHPMCOUNTER18 ,MHPMCOUNTER19 ,MHPMCOUNTER20 ,MHPMCOUNTER21 ,MHPMCOUNTER22 ,MHPMCOUNTER23 ,MHPMCOUNTER24 ,MHPMCOUNTER25 ,MHPMCOUNTER26 ,MHPMCOUNTER27 ,MHPMCOUNTER28 ,MHPMCOUNTER29 ,MHPMCOUNTER30 ,MHPMCOUNTER31 ,MHPMCOUNTERH3 ,MHPMCOUNTERH4 ,MHPMCOUNTERH5 ,MHPMCOUNTERH6 ,MHPMCOUNTERH7 ,MHPMCOUNTERH8 ,MHPMCOUNTERH9 ,MHPMCOUNTERH10 ,MHPMCOUNTERH11 ,MHPMCOUNTERH12 ,MHPMCOUNTERH13 ,MHPMCOUNTERH14 ,MHPMCOUNTERH15 ,MHPMCOUNTERH16 ,MHPMCOUNTERH17 ,MHPMCOUNTERH18 ,MHPMCOUNTERH19 ,MHPMCOUNTERH20 ,MHPMCOUNTERH21 ,MHPMCOUNTERH22 ,MHPMCOUNTERH23 ,MHPMCOUNTERH24 ,MHPMCOUNTERH25 ,MHPMCOUNTERH26 ,MHPMCOUNTERH27 ,MHPMCOUNTERH28 ,MHPMCOUNTERH29 ,MHPMCOUNTERH30 ,MHPMCOUNTERH31 ,
    ##########################
    #MSTATUS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd13933c1}
    ##########################
    #MSTATUS Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x300, x3

    #MSTATUS read value, expected 0x807fffea
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value, expected 0x0
    csrr x14, 0x300

    #MSTATUS Write value 0x55555555
    li x3, 0x55555555
    csrw 0x300, x3

    #MSTATUS read value, expected 0x555540
    csrr x14, 0x300

    #MSTATUS Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x300, x3

    #MSTATUS read value, expected 0x802aaaaa
    csrr x14, 0x300

    #MSTATUS Write value 0xd13933c1
    li x3, 0xd13933c1
    csrw 0x300, x3

    #MSTATUS read value, expected 0x803933c0
    csrr x14, 0x300

    ##########################
    #MTVEC testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h30d053db}
    ##########################
    #MTVEC Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x305, x3

    #MTVEC read value, expected 0xffffffff
    csrr x14, 0x305

    #MTVEC Write value 0x0
    li x3, 0x0
    csrw 0x305, x3

    #MTVEC read value, expected 0x0
    csrr x14, 0x305

    #MTVEC Write value 0x55555555
    li x3, 0x55555555
    csrw 0x305, x3

    #MTVEC read value, expected 0x55555555
    csrr x14, 0x305

    #MTVEC Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x305, x3

    #MTVEC read value, expected 0xaaaaaaaa
    csrr x14, 0x305

    #MTVEC Write value 0x30d053db
    li x3, 0x30d053db
    csrw 0x305, x3

    #MTVEC read value, expected 0x30d053db
    csrr x14, 0x305

    ##########################
    #MINSTRET testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb88086b0}
    ##########################
    #MINSTRET Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb02, x3

    #MINSTRET read value, expected 0xffffffff
    csrr x14, 0xb02

    #MINSTRET Write value 0x0
    li x3, 0x0
    csrw 0xb02, x3

    #MINSTRET read value, expected 0x0
    csrr x14, 0xb02

    #MINSTRET Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb02, x3

    #MINSTRET read value, expected 0x55555555
    csrr x14, 0xb02

    #MINSTRET Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb02, x3

    #MINSTRET read value, expected 0xaaaaaaaa
    csrr x14, 0xb02

    #MINSTRET Write value 0xb88086b0
    li x3, 0xb88086b0
    csrw 0xb02, x3

    #MINSTRET read value, expected 0xb88086b0
    csrr x14, 0xb02

    ##########################
    #MIE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfef91206}
    ##########################
    #MIE Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x304, x3

    #MIE read value, expected 0xbbb
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value, expected 0x0
    csrr x14, 0x304

    #MIE Write value 0x55555555
    li x3, 0x55555555
    csrw 0x304, x3

    #MIE read value, expected 0x111
    csrr x14, 0x304

    #MIE Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x304, x3

    #MIE read value, expected 0xaaa
    csrr x14, 0x304

    #MIE Write value 0xfef91206
    li x3, 0xfef91206
    csrw 0x304, x3

    #MIE read value, expected 0x202
    csrr x14, 0x304

    ##########################
    #MIP testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd3052355}
    ##########################
    #MIP Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x344, x3

    #MIP read value, expected 0xbbb
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value, expected 0x0
    csrr x14, 0x344

    #MIP Write value 0x55555555
    li x3, 0x55555555
    csrw 0x344, x3

    #MIP read value, expected 0x111
    csrr x14, 0x344

    #MIP Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x344, x3

    #MIP read value, expected 0xaaa
    csrr x14, 0x344

    #MIP Write value 0xd3052355
    li x3, 0xd3052355
    csrw 0x344, x3

    #MIP read value, expected 0x311
    csrr x14, 0x344

    ##########################
    #MEPC testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7238da3e}
    ##########################
    #MEPC Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x341, x3

    #MEPC read value, expected 0xffffffff
    csrr x14, 0x341

    #MEPC Write value 0x0
    li x3, 0x0
    csrw 0x341, x3

    #MEPC read value, expected 0x0
    csrr x14, 0x341

    #MEPC Write value 0x55555555
    li x3, 0x55555555
    csrw 0x341, x3

    #MEPC read value, expected 0x55555555
    csrr x14, 0x341

    #MEPC Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x341, x3

    #MEPC read value, expected 0xaaaaaaaa
    csrr x14, 0x341

    #MEPC Write value 0x7238da3e
    li x3, 0x7238da3e
    csrw 0x341, x3

    #MEPC read value, expected 0x7238da3e
    csrr x14, 0x341

    ##########################
    #MCYCLEH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7572495f}
    ##########################
    #MCYCLEH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb80, x3

    #MCYCLEH read value, expected 0xffffffff
    csrr x14, 0xb80

    #MCYCLEH Write value 0x0
    li x3, 0x0
    csrw 0xb80, x3

    #MCYCLEH read value, expected 0x0
    csrr x14, 0xb80

    #MCYCLEH Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb80, x3

    #MCYCLEH read value, expected 0x55555555
    csrr x14, 0xb80

    #MCYCLEH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb80, x3

    #MCYCLEH read value, expected 0xaaaaaaaa
    csrr x14, 0xb80

    #MCYCLEH Write value 0x7572495f
    li x3, 0x7572495f
    csrw 0xb80, x3

    #MCYCLEH read value, expected 0x7572495f
    csrr x14, 0xb80

    ##########################
    #MINSTRETH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he0f0095e}
    ##########################
    #MINSTRETH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb82, x3

    #MINSTRETH read value, expected 0xffffffff
    csrr x14, 0xb82

    #MINSTRETH Write value 0x0
    li x3, 0x0
    csrw 0xb82, x3

    #MINSTRETH read value, expected 0x0
    csrr x14, 0xb82

    #MINSTRETH Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb82, x3

    #MINSTRETH read value, expected 0x55555555
    csrr x14, 0xb82

    #MINSTRETH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb82, x3

    #MINSTRETH read value, expected 0xaaaaaaaa
    csrr x14, 0xb82

    #MINSTRETH Write value 0xe0f0095e
    li x3, 0xe0f0095e
    csrw 0xb82, x3

    #MINSTRETH read value, expected 0xe0f0095e
    csrr x14, 0xb82

    ##########################
    #MCAUSE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd43e7a20}
    ##########################
    #MCAUSE Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x342, x3

    #MCAUSE read value, expected 0xffffffff
    csrr x14, 0x342

    #MCAUSE Write value 0x0
    li x3, 0x0
    csrw 0x342, x3

    #MCAUSE read value, expected 0x0
    csrr x14, 0x342

    #MCAUSE Write value 0x55555555
    li x3, 0x55555555
    csrw 0x342, x3

    #MCAUSE read value, expected 0x55555555
    csrr x14, 0x342

    #MCAUSE Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x342, x3

    #MCAUSE read value, expected 0xaaaaaaaa
    csrr x14, 0x342

    #MCAUSE Write value 0xd43e7a20
    li x3, 0xd43e7a20
    csrw 0x342, x3

    #MCAUSE read value, expected 0xd43e7a20
    csrr x14, 0x342

    ##########################
    #MISA testing W/R values '{'hfdbf7bfb, 'h2408404, 'h55555555, 'haaaaaaaa, 'h2f0d4a6b}
    ##########################
    #MISA Write value 0xfdbf7bfb
    li x3, 0xfdbf7bfb
    csrw 0x301, x3

    #MISA read value, expected 0xc1bf7bfb
    csrr x14, 0x301

    #MISA Write value 0x2408404
    li x3, 0x2408404
    csrw 0x301, x3

    #MISA read value, expected 0x2408404
    csrr x14, 0x301

    #MISA Write value 0x55555555
    li x3, 0x55555555
    csrw 0x301, x3

    #MISA read value, expected 0x41555555
    csrr x14, 0x301

    #MISA Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x301, x3

    #MISA read value, expected 0x82aaaaaa
    csrr x14, 0x301

    #MISA Write value 0x2f0d4a6b
    li x3, 0x2f0d4a6b
    csrw 0x301, x3

    #MISA read value, expected 0x30d4a6b
    csrr x14, 0x301

    ##########################
    #MCYCLE testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbfbcce35}
    ##########################
    #MCYCLE Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0xb00, x3

    #MCYCLE read value, expected 0xffffffff
    csrr x14, 0xb00

    #MCYCLE Write value 0x0
    li x3, 0x0
    csrw 0xb00, x3

    #MCYCLE read value, expected 0x0
    csrr x14, 0xb00

    #MCYCLE Write value 0x55555555
    li x3, 0x55555555
    csrw 0xb00, x3

    #MCYCLE read value, expected 0x55555555
    csrr x14, 0xb00

    #MCYCLE Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0xb00, x3

    #MCYCLE read value, expected 0xaaaaaaaa
    csrr x14, 0xb00

    #MCYCLE Write value 0xbfbcce35
    li x3, 0xbfbcce35
    csrw 0xb00, x3

    #MCYCLE read value, expected 0xbfbcce35
    csrr x14, 0xb00

    ##########################
    #MSCRATCH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5334c7f3}
    ##########################
    #MSCRATCH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x340, x3

    #MSCRATCH read value, expected 0xffffffff
    csrr x14, 0x340

    #MSCRATCH Write value 0x0
    li x3, 0x0
    csrw 0x340, x3

    #MSCRATCH read value, expected 0x0
    csrr x14, 0x340

    #MSCRATCH Write value 0x55555555
    li x3, 0x55555555
    csrw 0x340, x3

    #MSCRATCH read value, expected 0x55555555
    csrr x14, 0x340

    #MSCRATCH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x340, x3

    #MSCRATCH read value, expected 0xaaaaaaaa
    csrr x14, 0x340

    #MSCRATCH Write value 0x5334c7f3
    li x3, 0x5334c7f3
    csrw 0x340, x3

    #MSCRATCH read value, expected 0x5334c7f3
    csrr x14, 0x340

    ##########################
    #MSTATUSH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6391f8b7}
    ##########################
    #MSTATUSH Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x310, x3

    #MSTATUSH read value, expected 0x30
    csrr x14, 0x310

    #MSTATUSH Write value 0x0
    li x3, 0x0
    csrw 0x310, x3

    #MSTATUSH read value, expected 0x0
    csrr x14, 0x310

    #MSTATUSH Write value 0x55555555
    li x3, 0x55555555
    csrw 0x310, x3

    #MSTATUSH read value, expected 0x10
    csrr x14, 0x310

    #MSTATUSH Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x310, x3

    #MSTATUSH read value, expected 0x20
    csrr x14, 0x310

    #MSTATUSH Write value 0x6391f8b7
    li x3, 0x6391f8b7
    csrw 0x310, x3

    #MSTATUSH read value, expected 0x30
    csrr x14, 0x310

    ##########################
    #MTVAL testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h973a306b}
    ##########################
    #MTVAL Write value 0xffffffff
    li x3, 0xffffffff
    csrw 0x343, x3

    #MTVAL read value, expected 0xffffffff
    csrr x14, 0x343

    #MTVAL Write value 0x0
    li x3, 0x0
    csrw 0x343, x3

    #MTVAL read value, expected 0x0
    csrr x14, 0x343

    #MTVAL Write value 0x55555555
    li x3, 0x55555555
    csrw 0x343, x3

    #MTVAL read value, expected 0x55555555
    csrr x14, 0x343

    #MTVAL Write value 0xaaaaaaaa
    li x3, 0xaaaaaaaa
    csrw 0x343, x3

    #MTVAL read value, expected 0xaaaaaaaa
    csrr x14, 0x343

    #MTVAL Write value 0x973a306b
    li x3, 0x973a306b
    csrw 0x343, x3

    #MTVAL read value, expected 0x973a306b
    csrr x14, 0x343

    ret
