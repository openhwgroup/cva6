# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

csrrw_fields:
    #Start CSR tests: Write/Read all registers fields with all values
    #User ignored registers: 

    ##########################
    #MHPMCOUNTER5 fields testing W/R
    ##########################
    #MHPMCOUNTER5.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdaf16bd8} 
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

    #MHPMCOUNTER5 Write value 0xdaf16bd8
    li x3, 0xdaf16bd8
    csrw 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #INSTRET WR skipped since it's a RO register

    ##########################
    #MTVEC fields testing W/R
    ##########################
    #MTVEC.MODE testing W/R values '{'h3, 'h0, 'h1, 'h2, 'h0} 
    #MTVEC Write value 0x3
    li x3, 0x3
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0x0
    li x3, 0x0
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0x1
    li x3, 0x1
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0x2
    li x3, 0x2
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0x0
    li x3, 0x0
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC.BASE testing W/R values '{'h3fffffff, 'h0, 'h15555555, 'h2aaaaaaa, 'h2cacb59} 
    #MTVEC Write value 0xfffffffc
    li x3, 0xfffffffc
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0x0
    li x3, 0x0
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0x55555554
    li x3, 0x55555554
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0xaaaaaaa8
    li x3, 0xaaaaaaa8
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write value 0xb2b2d64
    li x3, 0xb2b2d64
    csrw 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    ##########################
    #MHPMCOUNTER24 fields testing W/R
    ##########################
    #MHPMCOUNTER24.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2df24ab1} 
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

    #MHPMCOUNTER24 Write value 0x2df24ab1
    li x3, 0x2df24ab1
    csrw 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    ##########################
    #MHPMCOUNTER27 fields testing W/R
    ##########################
    #MHPMCOUNTER27.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfef91206} 
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

    #MHPMCOUNTER27 Write value 0xfef91206
    li x3, 0xfef91206
    csrw 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    ##########################
    #MHPMEVENT21 fields testing W/R
    ##########################
    #MHPMEVENT21.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd3052355} 
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

    #MHPMEVENT21 Write value 0xd3052355
    li x3, 0xd3052355
    csrw 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    ##########################
    #MHPMEVENT20 fields testing W/R
    ##########################
    #MHPMEVENT20.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7238da3e} 
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

    #MHPMEVENT20 Write value 0x7238da3e
    li x3, 0x7238da3e
    csrw 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    ##########################
    #PMPADDR2 fields testing W/R
    ##########################
    #PMPADDR2.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3ffdeebc} 
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

    #PMPADDR2 Write value 0x3ffdeebc
    li x3, 0x3ffdeebc
    csrw 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    ##########################
    #MHPMCOUNTER10 fields testing W/R
    ##########################
    #MHPMCOUNTER10.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb16b425c} 
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

    #MHPMCOUNTER10 Write value 0xb16b425c
    li x3, 0xb16b425c
    csrw 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    ##########################
    #MINSTRET fields testing W/R
    ##########################
    #MINSTRET.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha96b09c7} 
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

    #MINSTRET Write value 0xa96b09c7
    li x3, 0xa96b09c7
    csrw 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    ##########################
    #MHPMCOUNTERH14 fields testing W/R
    ##########################
    #MHPMCOUNTERH14.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5f2a4f0c} 
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

    #MHPMCOUNTERH14 Write value 0x5f2a4f0c
    li x3, 0x5f2a4f0c
    csrw 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    ##########################
    #MHPMEVENT6 fields testing W/R
    ##########################
    #MHPMEVENT6.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7572495f} 
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

    #MHPMEVENT6 Write value 0x7572495f
    li x3, 0x7572495f
    csrw 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    ##########################
    #MHPMEVENT26 fields testing W/R
    ##########################
    #MHPMEVENT26.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he0f0095e} 
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

    #MHPMEVENT26 Write value 0xe0f0095e
    li x3, 0xe0f0095e
    csrw 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    ##########################
    #MHPMEVENT16 fields testing W/R
    ##########################
    #MHPMEVENT16.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd13933c1} 
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

    #MHPMEVENT16 Write value 0xd13933c1
    li x3, 0xd13933c1
    csrw 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    ##########################
    #MHPMCOUNTERH17 fields testing W/R
    ##########################
    #MHPMCOUNTERH17.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd43e7a20} 
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

    #MHPMCOUNTERH17 Write value 0xd43e7a20
    li x3, 0xd43e7a20
    csrw 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    ##########################
    #MHPMEVENT19 fields testing W/R
    ##########################
    #MHPMEVENT19.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbd5dfae} 
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

    #MHPMEVENT19 Write value 0xbd5dfae
    li x3, 0xbd5dfae
    csrw 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #CYCLE WR skipped since it's a RO register

    ##########################
    #MIE fields testing W/R
    ##########################
    #MIE.USIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MIE Write value 0x1
    li x3, 0x1
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x1
    li x3, 0x1
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x1
    li x3, 0x1
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE.SSIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIE Write value 0x2
    li x3, 0x2
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x2
    li x3, 0x2
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE.MSIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIE Write value 0x8
    li x3, 0x8
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x8
    li x3, 0x8
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE.UTIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIE Write value 0x10
    li x3, 0x10
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x10
    li x3, 0x10
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE.STIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIE Write value 0x20
    li x3, 0x20
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x20
    li x3, 0x20
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE.MTIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIE Write value 0x80
    li x3, 0x80
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x80
    li x3, 0x80
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE.UEIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MIE Write value 0x100
    li x3, 0x100
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x100
    li x3, 0x100
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x100
    li x3, 0x100
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE.SEIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MIE Write value 0x200
    li x3, 0x200
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x200
    li x3, 0x200
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x200
    li x3, 0x200
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE.MEIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIE Write value 0x800
    li x3, 0x800
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x800
    li x3, 0x800
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write value 0x0
    li x3, 0x0
    csrw 0x304, x3

    #MIE read value
    csrr x14, 0x304

    ##########################
    #PMPADDR14 fields testing W/R
    ##########################
    #PMPADDR14.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbfbcce35} 
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

    #PMPADDR14 Write value 0xbfbcce35
    li x3, 0xbfbcce35
    csrw 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    ##########################
    #MHPMCOUNTERH18 fields testing W/R
    ##########################
    #MHPMCOUNTERH18.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5334c7f3} 
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

    #MHPMCOUNTERH18 Write value 0x5334c7f3
    li x3, 0x5334c7f3
    csrw 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    ##########################
    #MIP fields testing W/R
    ##########################
    #MIP.USIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MIP Write value 0x1
    li x3, 0x1
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x1
    li x3, 0x1
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x1
    li x3, 0x1
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP.SSIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIP Write value 0x2
    li x3, 0x2
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x2
    li x3, 0x2
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP.MSIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIP Write value 0x8
    li x3, 0x8
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x8
    li x3, 0x8
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP.UTIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIP Write value 0x10
    li x3, 0x10
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x10
    li x3, 0x10
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP.STIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MIP Write value 0x20
    li x3, 0x20
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x20
    li x3, 0x20
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x20
    li x3, 0x20
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP.MTIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIP Write value 0x80
    li x3, 0x80
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x80
    li x3, 0x80
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP.UEIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MIP Write value 0x100
    li x3, 0x100
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x100
    li x3, 0x100
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x100
    li x3, 0x100
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP.SEIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIP Write value 0x200
    li x3, 0x200
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x200
    li x3, 0x200
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP.MEIP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MIP Write value 0x800
    li x3, 0x800
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x800
    li x3, 0x800
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write value 0x0
    li x3, 0x0
    csrw 0x344, x3

    #MIP read value
    csrr x14, 0x344

    ##########################
    #MHPMCOUNTERH24 fields testing W/R
    ##########################
    #MHPMCOUNTERH24.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6391f8b7} 
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

    #MHPMCOUNTERH24 Write value 0x6391f8b7
    li x3, 0x6391f8b7
    csrw 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    ##########################
    #MHPMCOUNTERH23 fields testing W/R
    ##########################
    #MHPMCOUNTERH23.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h676adf55} 
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

    #MHPMCOUNTERH23 Write value 0x676adf55
    li x3, 0x676adf55
    csrw 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    ##########################
    #MEPC fields testing W/R
    ##########################
    #MEPC.MEPC testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd930ad96} 
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

    #MEPC Write value 0xd930ad96
    li x3, 0xd930ad96
    csrw 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    ##########################
    #MHPMEVENT4 fields testing W/R
    ##########################
    #MHPMEVENT4.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h136ce448} 
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

    #MHPMEVENT4 Write value 0x136ce448
    li x3, 0x136ce448
    csrw 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    ##########################
    #PMPADDR0 fields testing W/R
    ##########################
    #PMPADDR0.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb61f0663} 
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

    #PMPADDR0 Write value 0xb61f0663
    li x3, 0xb61f0663
    csrw 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #MHARTID WR skipped since it's a RO register

    #MVENDORID WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTER3 fields testing W/R
    ##########################
    #MHPMCOUNTER3.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4b458ffd} 
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

    #MHPMCOUNTER3 Write value 0x4b458ffd
    li x3, 0x4b458ffd
    csrw 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #CYCLEH WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTER4 fields testing W/R
    ##########################
    #MHPMCOUNTER4.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h856a15b2} 
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

    #MHPMCOUNTER4 Write value 0x856a15b2
    li x3, 0x856a15b2
    csrw 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    ##########################
    #MHPMEVENT15 fields testing W/R
    ##########################
    #MHPMEVENT15.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h8002014b} 
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

    #MHPMEVENT15 Write value 0x8002014b
    li x3, 0x8002014b
    csrw 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MARCHID WR skipped since it's a RO register

    ##########################
    #PMPADDR4 fields testing W/R
    ##########################
    #PMPADDR4.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6a8c2f49} 
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

    #PMPADDR4 Write value 0x6a8c2f49
    li x3, 0x6a8c2f49
    csrw 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    ##########################
    #MHPMCOUNTER20 fields testing W/R
    ##########################
    #MHPMCOUNTER20.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfb1ee89} 
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

    #MHPMCOUNTER20 Write value 0xfb1ee89
    li x3, 0xfb1ee89
    csrw 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    ##########################
    #MHPMEVENT27 fields testing W/R
    ##########################
    #MHPMEVENT27.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h4db6008a} 
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

    #MHPMEVENT27 Write value 0x4db6008a
    li x3, 0x4db6008a
    csrw 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    ##########################
    #PMPADDR13 fields testing W/R
    ##########################
    #PMPADDR13.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc73c8ac2} 
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

    #PMPADDR13 Write value 0xc73c8ac2
    li x3, 0xc73c8ac2
    csrw 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    ##########################
    #MCYCLEH fields testing W/R
    ##########################
    #MCYCLEH.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hac2ea0b2} 
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

    #MCYCLEH Write value 0xac2ea0b2
    li x3, 0xac2ea0b2
    csrw 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    ##########################
    #MHPMEVENT24 fields testing W/R
    ##########################
    #MHPMEVENT24.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2fa5ef0b} 
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

    #MHPMEVENT24 Write value 0x2fa5ef0b
    li x3, 0x2fa5ef0b
    csrw 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    ##########################
    #MHPMCOUNTERH9 fields testing W/R
    ##########################
    #MHPMCOUNTERH9.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha9be0e41} 
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

    #MHPMCOUNTERH9 Write value 0xa9be0e41
    li x3, 0xa9be0e41
    csrw 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    ##########################
    #MHPMEVENT25 fields testing W/R
    ##########################
    #MHPMEVENT25.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h94477785} 
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

    #MHPMEVENT25 Write value 0x94477785
    li x3, 0x94477785
    csrw 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    ##########################
    #PMPADDR7 fields testing W/R
    ##########################
    #PMPADDR7.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h78e1e1d9} 
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

    #PMPADDR7 Write value 0x78e1e1d9
    li x3, 0x78e1e1d9
    csrw 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    ##########################
    #MINSTRETH fields testing W/R
    ##########################
    #MINSTRETH.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h32e6b405} 
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

    #MINSTRETH Write value 0x32e6b405
    li x3, 0x32e6b405
    csrw 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    ##########################
    #MHPMEVENT31 fields testing W/R
    ##########################
    #MHPMEVENT31.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbf901c35} 
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

    #MHPMEVENT31 Write value 0xbf901c35
    li x3, 0xbf901c35
    csrw 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    ##########################
    #MHPMCOUNTER18 fields testing W/R
    ##########################
    #MHPMCOUNTER18.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3d95cb2c} 
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

    #MHPMCOUNTER18 Write value 0x3d95cb2c
    li x3, 0x3d95cb2c
    csrw 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    ##########################
    #MHPMCOUNTERH13 fields testing W/R
    ##########################
    #MHPMCOUNTERH13.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h68886bd5} 
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

    #MHPMCOUNTERH13 Write value 0x68886bd5
    li x3, 0x68886bd5
    csrw 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    ##########################
    #PMPADDR11 fields testing W/R
    ##########################
    #PMPADDR11.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdd8b75dd} 
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

    #PMPADDR11 Write value 0xdd8b75dd
    li x3, 0xdd8b75dd
    csrw 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    ##########################
    #MHPMCOUNTER25 fields testing W/R
    ##########################
    #MHPMCOUNTER25.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h75b2bf13} 
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

    #MHPMCOUNTER25 Write value 0x75b2bf13
    li x3, 0x75b2bf13
    csrw 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    ##########################
    #MHPMCOUNTERH19 fields testing W/R
    ##########################
    #MHPMCOUNTERH19.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h906755d9} 
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

    #MHPMCOUNTERH19 Write value 0x906755d9
    li x3, 0x906755d9
    csrw 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    ##########################
    #ICACHE fields testing W/R
    ##########################
    #ICACHE.ICACHE testing W/R values '{'h0, 'h1, 'h1, 'h0, 'h0} 
    #ICACHE Write value 0x0
    li x3, 0x0
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write value 0x1
    li x3, 0x1
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write value 0x1
    li x3, 0x1
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write value 0x0
    li x3, 0x0
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write value 0x0
    li x3, 0x0
    csrw 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    ##########################
    #MHPMEVENT23 fields testing W/R
    ##########################
    #MHPMEVENT23.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hf38c4202} 
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

    #MHPMEVENT23 Write value 0xf38c4202
    li x3, 0xf38c4202
    csrw 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    ##########################
    #MHPMCOUNTER28 fields testing W/R
    ##########################
    #MHPMCOUNTER28.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6fba4c85} 
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

    #MHPMCOUNTER28 Write value 0x6fba4c85
    li x3, 0x6fba4c85
    csrw 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    ##########################
    #MHPMCOUNTERH31 fields testing W/R
    ##########################
    #MHPMCOUNTERH31.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5e5a845d} 
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

    #MHPMCOUNTERH31 Write value 0x5e5a845d
    li x3, 0x5e5a845d
    csrw 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    ##########################
    #MHPMEVENT22 fields testing W/R
    ##########################
    #MHPMEVENT22.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h63d7b81f} 
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

    #MHPMEVENT22 Write value 0x63d7b81f
    li x3, 0x63d7b81f
    csrw 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    ##########################
    #MHPMCOUNTER13 fields testing W/R
    ##########################
    #MHPMCOUNTER13.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hebd7ae64} 
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

    #MHPMCOUNTER13 Write value 0xebd7ae64
    li x3, 0xebd7ae64
    csrw 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    ##########################
    #PMPCFG3 fields testing W/R
    ##########################
    #PMPCFG3.PMP12CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'h9} 
    #PMPCFG3 Write value 0xff
    li x3, 0xff
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x0
    li x3, 0x0
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x55
    li x3, 0x55
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0xaa
    li x3, 0xaa
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x9
    li x3, 0x9
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3.PMP13CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'hf3} 
    #PMPCFG3 Write value 0xff00
    li x3, 0xff00
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x0
    li x3, 0x0
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x5500
    li x3, 0x5500
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0xaa00
    li x3, 0xaa00
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0xf300
    li x3, 0xf300
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3.PMP14CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'hf9} 
    #PMPCFG3 Write value 0xff0000
    li x3, 0xff0000
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x0
    li x3, 0x0
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x550000
    li x3, 0x550000
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0xaa0000
    li x3, 0xaa0000
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0xf90000
    li x3, 0xf90000
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3.PMP15CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'hc} 
    #PMPCFG3 Write value 0xff000000
    li x3, 0xff000000
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x0
    li x3, 0x0
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0x55000000
    li x3, 0x55000000
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0xaa000000
    li x3, 0xaa000000
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write value 0xc000000
    li x3, 0xc000000
    csrw 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    ##########################
    #PMPADDR8 fields testing W/R
    ##########################
    #PMPADDR8.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h92c65398} 
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

    #PMPADDR8 Write value 0x92c65398
    li x3, 0x92c65398
    csrw 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    ##########################
    #MHPMCOUNTERH27 fields testing W/R
    ##########################
    #MHPMCOUNTERH27.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hf8cc9174} 
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

    #MHPMCOUNTERH27 Write value 0xf8cc9174
    li x3, 0xf8cc9174
    csrw 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    ##########################
    #MHPMCOUNTER15 fields testing W/R
    ##########################
    #MHPMCOUNTER15.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7f4c9726} 
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

    #MHPMCOUNTER15 Write value 0x7f4c9726
    li x3, 0x7f4c9726
    csrw 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    ##########################
    #PMPCFG0 fields testing W/R
    ##########################
    #PMPCFG0.PMP0CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'h79} 
    #PMPCFG0 Write value 0x00088808
    li x3, 0x00088808
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xff
    li x3, 0xff
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x0
    li x3, 0x0
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x55
    li x3, 0x55
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xaa
    li x3, 0xaa
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x79
    li x3, 0x79
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0.PMP1CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'hcd}
    #PMPCFG0 Write value 0xff00
    li x3, 0xff00
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x0
    li x3, 0x0
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x5500
    li x3, 0x5500
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xaa00
    li x3, 0xaa00
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xcd00
    li x3, 0xcd00
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0.PMP2CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'h38} 
    #PMPCFG0 Write value 0xff0000
    li x3, 0xff0000
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x0
    li x3, 0x0
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x550000
    li x3, 0x550000
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xaa0000
    li x3, 0xaa0000
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x380000
    li x3, 0x380000
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0.PMP3CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'hff} 
    #PMPCFG0 Write value 0xff000000
    li x3, 0xff000000
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x0
    li x3, 0x0
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0x55000000
    li x3, 0x55000000
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xaa000000
    li x3, 0xaa000000
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write value 0xff000000
    li x3, 0xff000000
    csrw 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    ##########################
    #MHPMCOUNTER14 fields testing W/R
    ##########################
    #MHPMCOUNTER14.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h5ba2d023} 
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

    #MHPMCOUNTER14 Write value 0x5ba2d023
    li x3, 0x5ba2d023
    csrw 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    ##########################
    #MHPMCOUNTER22 fields testing W/R
    ##########################
    #MHPMCOUNTER22.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3df5de65} 
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

    #MHPMCOUNTER22 Write value 0x3df5de65
    li x3, 0x3df5de65
    csrw 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    ##########################
    #MHPMCOUNTER26 fields testing W/R
    ##########################
    #MHPMCOUNTER26.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h696f5835} 
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

    #MHPMCOUNTER26 Write value 0x696f5835
    li x3, 0x696f5835
    csrw 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    ##########################
    #MHPMCOUNTERH7 fields testing W/R
    ##########################
    #MHPMCOUNTERH7.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h35faa941} 
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

    #MHPMCOUNTERH7 Write value 0x35faa941
    li x3, 0x35faa941
    csrw 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    ##########################
    #MHPMCOUNTER21 fields testing W/R
    ##########################
    #MHPMCOUNTER21.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc99bb27} 
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

    #MHPMCOUNTER21 Write value 0xc99bb27
    li x3, 0xc99bb27
    csrw 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    ##########################
    #MSTATUS fields testing W/R
    ##########################
    #MSTATUS.SIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MSTATUS Write value 0x2
    li x3, 0x2
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x2
    li x3, 0x2
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.MIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MSTATUS Write value 0x8
    li x3, 0x8
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x8
    li x3, 0x8
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.SPIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUS Write value 0x20
    li x3, 0x20
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x20
    li x3, 0x20
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x20
    li x3, 0x20
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.UBE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUS Write value 0x40
    li x3, 0x40
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x40
    li x3, 0x40
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x40
    li x3, 0x40
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.MPIE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUS Write value 0x80
    li x3, 0x80
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x80
    li x3, 0x80
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x80
    li x3, 0x80
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.SPP testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MSTATUS Write value 0x100
    li x3, 0x100
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x100
    li x3, 0x100
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.VS testing W/R values '{'h3, 'h0, 'h1, 'h2, 'h3} 
    #MSTATUS Write value 0x600
    li x3, 0x600
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x200
    li x3, 0x200
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x400
    li x3, 0x400
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x600
    li x3, 0x600
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.MPP testing W/R values '{'h3, 'h0, 'h1, 'h2, 'h2} 
    #MSTATUS Write value 0x1800
    li x3, 0x1800
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x800
    li x3, 0x800
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x1000
    li x3, 0x1000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x1000
    li x3, 0x1000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.FS testing W/R values '{'h3, 'h0, 'h1, 'h2, 'h2} 
    #MSTATUS Write value 0x6000
    li x3, 0x6000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x2000
    li x3, 0x2000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x4000
    li x3, 0x4000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x4000
    li x3, 0x4000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.XS testing W/R values '{'h3, 'h0, 'h1, 'h2, 'h3} 
    #MSTATUS Write value 0x18000
    li x3, 0x18000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x8000
    li x3, 0x8000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x10000
    li x3, 0x10000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x18000
    li x3, 0x18000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.MPRV testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUS Write value 0x20000
    li x3, 0x20000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x20000
    li x3, 0x20000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x20000
    li x3, 0x20000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.SUM testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUS Write value 0x40000
    li x3, 0x40000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x40000
    li x3, 0x40000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x40000
    li x3, 0x40000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.MXR testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUS Write value 0x80000
    li x3, 0x80000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x80000
    li x3, 0x80000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x80000
    li x3, 0x80000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.TVM testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUS Write value 0x100000
    li x3, 0x100000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x100000
    li x3, 0x100000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x100000
    li x3, 0x100000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.TW testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MSTATUS Write value 0x200000
    li x3, 0x200000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x200000
    li x3, 0x200000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.TSR testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MSTATUS Write value 0x400000
    li x3, 0x400000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x400000
    li x3, 0x400000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS.SD testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUS Write value 0x80000000
    li x3, 0x80000000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x80000000
    li x3, 0x80000000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x0
    li x3, 0x0
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write value 0x80000000
    li x3, 0x80000000
    csrw 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    ##########################
    #MHPMCOUNTER7 fields testing W/R
    ##########################
    #MHPMCOUNTER7.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3724d5f2} 
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

    #MHPMCOUNTER7 Write value 0x3724d5f2
    li x3, 0x3724d5f2
    csrw 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    ##########################
    #MHPMCOUNTERH8 fields testing W/R
    ##########################
    #MHPMCOUNTERH8.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbf258eba} 
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

    #MHPMCOUNTERH8 Write value 0xbf258eba
    li x3, 0xbf258eba
    csrw 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    ##########################
    #MCAUSE fields testing W/R
    ##########################
    #MCAUSE.EXCEPTION_CODE testing W/R values '{'h7fffffff, 'h0, 'h55555555, 'h2aaaaaaa, 'h32b0e601} 
    #MCAUSE Write value 0x7fffffff
    li x3, 0x7fffffff
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

    #MCAUSE Write value 0x2aaaaaaa
    li x3, 0x2aaaaaaa
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0x32b0e601
    li x3, 0x32b0e601
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE.INTERRUPT testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MCAUSE Write value 0x80000000
    li x3, 0x80000000
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0x0
    li x3, 0x0
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0x80000000
    li x3, 0x80000000
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0x0
    li x3, 0x0
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write value 0x80000000
    li x3, 0x80000000
    csrw 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    ##########################
    #MHPMEVENT5 fields testing W/R
    ##########################
    #MHPMEVENT5.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6ecdba45} 
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

    #MHPMEVENT5 Write value 0x6ecdba45
    li x3, 0x6ecdba45
    csrw 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    ##########################
    #PMPADDR10 fields testing W/R
    ##########################
    #PMPADDR10.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc72f23fa} 
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

    #PMPADDR10 Write value 0xc72f23fa
    li x3, 0xc72f23fa
    csrw 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    ##########################
    #PMPCFG2 fields testing W/R
    ##########################
    #PMPCFG2.PMP8CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'he3} 
    #PMPCFG2 Write value 0xff
    li x3, 0xff
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x0
    li x3, 0x0
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x55
    li x3, 0x55
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0xaa
    li x3, 0xaa
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0xe3
    li x3, 0xe3
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2.PMP9CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'h6f} 
    #PMPCFG2 Write value 0xff00
    li x3, 0xff00
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x0
    li x3, 0x0
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x5500
    li x3, 0x5500
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0xaa00
    li x3, 0xaa00
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x6f00
    li x3, 0x6f00
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2.PMP10CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'h55} 
    #PMPCFG2 Write value 0xff0000
    li x3, 0xff0000
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x0
    li x3, 0x0
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x550000
    li x3, 0x550000
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0xaa0000
    li x3, 0xaa0000
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x550000
    li x3, 0x550000
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2.PMP11CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'h19} 
    #PMPCFG2 Write value 0xff000000
    li x3, 0xff000000
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x0
    li x3, 0x0
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x55000000
    li x3, 0x55000000
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0xaa000000
    li x3, 0xaa000000
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write value 0x19000000
    li x3, 0x19000000
    csrw 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #MIMPID WR skipped since it's a RO register

    ##########################
    #PMPADDR6 fields testing W/R
    ##########################
    #PMPADDR6.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hebaec342} 
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

    #PMPADDR6 Write value 0xebaec342
    li x3, 0xebaec342
    csrw 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    ##########################
    #MHPMCOUNTERH15 fields testing W/R
    ##########################
    #MHPMCOUNTERH15.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2ed9656e} 
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

    #MHPMCOUNTERH15 Write value 0x2ed9656e
    li x3, 0x2ed9656e
    csrw 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    ##########################
    #MHPMCOUNTERH28 fields testing W/R
    ##########################
    #MHPMCOUNTERH28.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h8d598a09} 
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

    #MHPMCOUNTERH28 Write value 0x8d598a09
    li x3, 0x8d598a09
    csrw 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #INSTRETH WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTER23 fields testing W/R
    ##########################
    #MHPMCOUNTER23.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha976311} 
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

    #MHPMCOUNTER23 Write value 0xa976311
    li x3, 0xa976311
    csrw 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    ##########################
    #PMPADDR5 fields testing W/R
    ##########################
    #PMPADDR5.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2b2e6d39} 
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

    #PMPADDR5 Write value 0x2b2e6d39
    li x3, 0x2b2e6d39
    csrw 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    ##########################
    #MISA fields testing W/R
    ##########################
    #MISA.EXTENSIONS testing W/R values '{'h1bf7bfb, 'h2408404, 'h1555555, 'h2aaaaaa, 'h37e8b96} 
    #MISA Write value 0x1bf7bfb
    li x3, 0x1bf7bfb
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x2408404
    li x3, 0x2408404
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x1555555
    li x3, 0x1555555
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x2aaaaaa
    li x3, 0x2aaaaaa
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x37e8b96
    li x3, 0x37e8b96
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA.MXL testing W/R values '{'h3, 'h0, 'h1, 'h2, 'h3} 
    #MISA Write value 0xc0000000
    li x3, 0xc0000000
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x0
    li x3, 0x0
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x40000000
    li x3, 0x40000000
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0x80000000
    li x3, 0x80000000
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write value 0xc0000000
    li x3, 0xc0000000
    csrw 0x301, x3

    #MISA read value
    csrr x14, 0x301

    ##########################
    #MHPMCOUNTERH12 fields testing W/R
    ##########################
    #MHPMCOUNTERH12.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb42aab4b} 
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

    #MHPMCOUNTERH12 Write value 0xb42aab4b
    li x3, 0xb42aab4b
    csrw 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    ##########################
    #MHPMCOUNTERH4 fields testing W/R
    ##########################
    #MHPMCOUNTERH4.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h656b6e8f} 
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

    #MHPMCOUNTERH4 Write value 0x656b6e8f
    li x3, 0x656b6e8f
    csrw 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    ##########################
    #MHPMEVENT3 fields testing W/R
    ##########################
    #MHPMEVENT3.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbb66394e} 
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

    #MHPMEVENT3 Write value 0xbb66394e
    li x3, 0xbb66394e
    csrw 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    ##########################
    #PMPCFG1 fields testing W/R
    ##########################
    #PMPCFG1.PMP4CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'h74} 
    #PMPCFG1 Write value 0xff
    li x3, 0xff
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x0
    li x3, 0x0
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x55
    li x3, 0x55
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0xaa
    li x3, 0xaa
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x74
    li x3, 0x74
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1.PMP5CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'hc1} 
    #PMPCFG1 Write value 0xff00
    li x3, 0xff00
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x0
    li x3, 0x0
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x5500
    li x3, 0x5500
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0xaa00
    li x3, 0xaa00
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0xc100
    li x3, 0xc100
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1.PMP6CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'h6f} 
    #PMPCFG1 Write value 0xff0000
    li x3, 0xff0000
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x0
    li x3, 0x0
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x550000
    li x3, 0x550000
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0xaa0000
    li x3, 0xaa0000
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x6f0000
    li x3, 0x6f0000
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1.PMP7CFG testing W/R values '{'hff, 'h0, 'h55, 'haa, 'hfd} 
    #PMPCFG1 Write value 0xff000000
    li x3, 0xff000000
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x0
    li x3, 0x0
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0x55000000
    li x3, 0x55000000
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0xaa000000
    li x3, 0xaa000000
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write value 0xfd000000
    li x3, 0xfd000000
    csrw 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    ##########################
    #MHPMEVENT13 fields testing W/R
    ##########################
    #MHPMEVENT13.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h921703ff} 
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

    #MHPMEVENT13 Write value 0x921703ff
    li x3, 0x921703ff
    csrw 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    ##########################
    #MHPMCOUNTER11 fields testing W/R
    ##########################
    #MHPMCOUNTER11.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2abb41c6} 
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

    #MHPMCOUNTER11 Write value 0x2abb41c6
    li x3, 0x2abb41c6
    csrw 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    ##########################
    #MHPMCOUNTER30 fields testing W/R
    ##########################
    #MHPMCOUNTER30.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h637ebf13} 
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

    #MHPMCOUNTER30 Write value 0x637ebf13
    li x3, 0x637ebf13
    csrw 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    ##########################
    #MCYCLE fields testing W/R
    ##########################
    #MCYCLE.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdd1284fe} 
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

    #MCYCLE Write value 0xdd1284fe
    li x3, 0xdd1284fe
    csrw 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    ##########################
    #MHPMCOUNTERH30 fields testing W/R
    ##########################
    #MHPMCOUNTERH30.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h2b9f8d7f} 
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

    #MHPMCOUNTERH30 Write value 0x2b9f8d7f
    li x3, 0x2b9f8d7f
    csrw 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    ##########################
    #PMPADDR15 fields testing W/R
    ##########################
    #PMPADDR15.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h93129383} 
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

    #PMPADDR15 Write value 0x93129383
    li x3, 0x93129383
    csrw 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    ##########################
    #MHPMCOUNTERH20 fields testing W/R
    ##########################
    #MHPMCOUNTERH20.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h69613ba2} 
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

    #MHPMCOUNTERH20 Write value 0x69613ba2
    li x3, 0x69613ba2
    csrw 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    ##########################
    #MHPMCOUNTER16 fields testing W/R
    ##########################
    #MHPMCOUNTER16.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h128a8bcb} 
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

    #MHPMCOUNTER16 Write value 0x128a8bcb
    li x3, 0x128a8bcb
    csrw 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    ##########################
    #MHPMEVENT12 fields testing W/R
    ##########################
    #MHPMEVENT12.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h97bb976f} 
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

    #MHPMEVENT12 Write value 0x97bb976f
    li x3, 0x97bb976f
    csrw 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    ##########################
    #MHPMCOUNTER12 fields testing W/R
    ##########################
    #MHPMCOUNTER12.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h6acc922c} 
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

    #MHPMCOUNTER12 Write value 0x6acc922c
    li x3, 0x6acc922c
    csrw 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    ##########################
    #MHPMCOUNTERH11 fields testing W/R
    ##########################
    #MHPMCOUNTERH11.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h87838f74} 
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

    #MHPMCOUNTERH11 Write value 0x87838f74
    li x3, 0x87838f74
    csrw 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    ##########################
    #MHPMEVENT8 fields testing W/R
    ##########################
    #MHPMEVENT8.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h84dfe6ab} 
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

    #MHPMEVENT8 Write value 0x84dfe6ab
    li x3, 0x84dfe6ab
    csrw 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    ##########################
    #MHPMCOUNTERH3 fields testing W/R
    ##########################
    #MHPMCOUNTERH3.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h8dd806e7} 
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

    #MHPMCOUNTERH3 Write value 0x8dd806e7
    li x3, 0x8dd806e7
    csrw 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    ##########################
    #MHPMCOUNTERH21 fields testing W/R
    ##########################
    #MHPMCOUNTERH21.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hd0af0166} 
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

    #MHPMCOUNTERH21 Write value 0xd0af0166
    li x3, 0xd0af0166
    csrw 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    ##########################
    #MHPMCOUNTER19 fields testing W/R
    ##########################
    #MHPMCOUNTER19.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h65de141a} 
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

    #MHPMCOUNTER19 Write value 0x65de141a
    li x3, 0x65de141a
    csrw 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    ##########################
    #MHPMCOUNTER29 fields testing W/R
    ##########################
    #MHPMCOUNTER29.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h72c1a7ee} 
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

    #MHPMCOUNTER29 Write value 0x72c1a7ee
    li x3, 0x72c1a7ee
    csrw 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    ##########################
    #MHPMEVENT18 fields testing W/R
    ##########################
    #MHPMEVENT18.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h68b40e56} 
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

    #MHPMEVENT18 Write value 0x68b40e56
    li x3, 0x68b40e56
    csrw 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    ##########################
    #MSCRATCH fields testing W/R
    ##########################
    #MSCRATCH.MSCRATCH testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h549139bb} 
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

    #MSCRATCH Write value 0x549139bb
    li x3, 0x549139bb
    csrw 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    ##########################
    #MHPMEVENT9 fields testing W/R
    ##########################
    #MHPMEVENT9.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h92832ef6} 
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

    #MHPMEVENT9 Write value 0x92832ef6
    li x3, 0x92832ef6
    csrw 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    ##########################
    #MHPMEVENT29 fields testing W/R
    ##########################
    #MHPMEVENT29.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha61ef0c3} 
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

    #MHPMEVENT29 Write value 0xa61ef0c3
    li x3, 0xa61ef0c3
    csrw 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    ##########################
    #MHPMEVENT17 fields testing W/R
    ##########################
    #MHPMEVENT17.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'ha3bdff18} 
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

    #MHPMEVENT17 Write value 0xa3bdff18
    li x3, 0xa3bdff18
    csrw 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    ##########################
    #MHPMCOUNTERH29 fields testing W/R
    ##########################
    #MHPMCOUNTERH29.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3ccaefe3} 
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

    #MHPMCOUNTERH29 Write value 0x3ccaefe3
    li x3, 0x3ccaefe3
    csrw 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    ##########################
    #MHPMCOUNTERH6 fields testing W/R
    ##########################
    #MHPMCOUNTERH6.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb54c9046} 
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

    #MHPMCOUNTERH6 Write value 0xb54c9046
    li x3, 0xb54c9046
    csrw 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    ##########################
    #MHPMCOUNTERH5 fields testing W/R
    ##########################
    #MHPMCOUNTERH5.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hbea28fd1} 
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

    #MHPMCOUNTERH5 Write value 0xbea28fd1
    li x3, 0xbea28fd1
    csrw 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    ##########################
    #MHPMEVENT14 fields testing W/R
    ##########################
    #MHPMEVENT14.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h189944b1} 
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

    #MHPMEVENT14 Write value 0x189944b1
    li x3, 0x189944b1
    csrw 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    ##########################
    #MHPMEVENT30 fields testing W/R
    ##########################
    #MHPMEVENT30.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hdaeefd2b} 
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

    #MHPMEVENT30 Write value 0xdaeefd2b
    li x3, 0xdaeefd2b
    csrw 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    ##########################
    #MSTATUSH fields testing W/R
    ##########################
    #MSTATUSH.SBE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h0} 
    #MSTATUSH Write value 0x10
    li x3, 0x10
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x0
    li x3, 0x0
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x10
    li x3, 0x10
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x0
    li x3, 0x0
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x0
    li x3, 0x0
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH.MBE testing W/R values '{'h1, 'h0, 'h1, 'h0, 'h1} 
    #MSTATUSH Write value 0x20
    li x3, 0x20
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x0
    li x3, 0x0
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x20
    li x3, 0x20
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x0
    li x3, 0x0
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write value 0x20
    li x3, 0x20
    csrw 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    ##########################
    #MHPMCOUNTER17 fields testing W/R
    ##########################
    #MHPMCOUNTER17.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h37d0c9d4} 
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

    #MHPMCOUNTER17 Write value 0x37d0c9d4
    li x3, 0x37d0c9d4
    csrw 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    ##########################
    #PMPADDR12 fields testing W/R
    ##########################
    #PMPADDR12.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h352a4d41} 
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

    #PMPADDR12 Write value 0x352a4d41
    li x3, 0x352a4d41
    csrw 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    ##########################
    #MHPMCOUNTER31 fields testing W/R
    ##########################
    #MHPMCOUNTER31.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfa7e4d8f} 
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

    #MHPMCOUNTER31 Write value 0xfa7e4d8f
    li x3, 0xfa7e4d8f
    csrw 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    ##########################
    #MHPMCOUNTER6 fields testing W/R
    ##########################
    #MHPMCOUNTER6.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h7fbc00c} 
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

    #MHPMCOUNTER6 Write value 0x7fbc00c
    li x3, 0x7fbc00c
    csrw 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    ##########################
    #MHPMCOUNTERH16 fields testing W/R
    ##########################
    #MHPMCOUNTERH16.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h3931500f} 
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

    #MHPMCOUNTERH16 Write value 0x3931500f
    li x3, 0x3931500f
    csrw 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    ##########################
    #MHPMEVENT28 fields testing W/R
    ##########################
    #MHPMEVENT28.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hc612ecd7} 
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

    #MHPMEVENT28 Write value 0xc612ecd7
    li x3, 0xc612ecd7
    csrw 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    ##########################
    #PMPADDR3 fields testing W/R
    ##########################
    #PMPADDR3.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he4b2985e} 
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

    #PMPADDR3 Write value 0xe4b2985e
    li x3, 0xe4b2985e
    csrw 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    ##########################
    #PMPADDR9 fields testing W/R
    ##########################
    #PMPADDR9.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'habb519fb} 
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

    #PMPADDR9 Write value 0xabb519fb
    li x3, 0xabb519fb
    csrw 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    ##########################
    #MHPMCOUNTER8 fields testing W/R
    ##########################
    #MHPMCOUNTER8.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h31bc25e4} 
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

    #MHPMCOUNTER8 Write value 0x31bc25e4
    li x3, 0x31bc25e4
    csrw 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    ##########################
    #MHPMCOUNTERH25 fields testing W/R
    ##########################
    #MHPMCOUNTERH25.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h525de923} 
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

    #MHPMCOUNTERH25 Write value 0x525de923
    li x3, 0x525de923
    csrw 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    ##########################
    #PMPADDR1 fields testing W/R
    ##########################
    #PMPADDR1.ADDRESS testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hebba3c2b} 
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

    #PMPADDR1 Write value 0xebba3c2b
    li x3, 0xebba3c2b
    csrw 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    ##########################
    #MHPMEVENT7 fields testing W/R
    ##########################
    #MHPMEVENT7.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hfa9a205} 
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

    #MHPMEVENT7 Write value 0xfa9a205
    li x3, 0xfa9a205
    csrw 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    ##########################
    #MHPMEVENT10 fields testing W/R
    ##########################
    #MHPMEVENT10.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he970598b} 
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

    #MHPMEVENT10 Write value 0xe970598b
    li x3, 0xe970598b
    csrw 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    ##########################
    #MHPMCOUNTERH10 fields testing W/R
    ##########################
    #MHPMCOUNTERH10.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'he47bf243} 
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

    #MHPMCOUNTERH10 Write value 0xe47bf243
    li x3, 0xe47bf243
    csrw 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    ##########################
    #MHPMCOUNTER9 fields testing W/R
    ##########################
    #MHPMCOUNTER9.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'h92944d3c} 
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

    #MHPMCOUNTER9 Write value 0x92944d3c
    li x3, 0x92944d3c
    csrw 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    ##########################
    #MHPMCOUNTERH22 fields testing W/R
    ##########################
    #MHPMCOUNTERH22.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hadbafa53} 
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

    #MHPMCOUNTERH22 Write value 0xadbafa53
    li x3, 0xadbafa53
    csrw 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    ##########################
    #MHPMCOUNTERH26 fields testing W/R
    ##########################
    #MHPMCOUNTERH26.COUNT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hcc60a7b7} 
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

    #MHPMCOUNTERH26 Write value 0xcc60a7b7
    li x3, 0xcc60a7b7
    csrw 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    ##########################
    #MHPMEVENT11 fields testing W/R
    ##########################
    #MHPMEVENT11.MHPMEVENT testing W/R values '{'hffffffff, 'h0, 'h55555555, 'haaaaaaaa, 'hb0b47671} 
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

    #MHPMEVENT11 Write value 0xb0b47671
    li x3, 0xb0b47671
    csrw 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    ret
