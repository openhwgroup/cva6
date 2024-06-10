# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

csrcsi:
    #Start CSR tests: Write/Read all RW registers in a random order using Clear/Set immediate instructions
    #User ignored registers: 

    ##########################
    #MTVAL testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hb}
    ##########################
    #MTVAL Write clear/set value 0x1f
    csrrci x14, 0x343, 0x0
    csrrsi x14, 0x343, 0x1f

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x0
    csrrci x14, 0x343, 0x1f
    csrrsi x14, 0x343, 0x0

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x15
    csrrci x14, 0x343, 0xa
    csrrsi x14, 0x343, 0x15

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write clear/set value 0xa
    csrrci x14, 0x343, 0x15
    csrrsi x14, 0x343, 0xa

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write clear/set value 0xb
    csrrci x14, 0x343, 0x14
    csrrsi x14, 0x343, 0xb

    #MTVAL read value
    csrr x14, 0x343

    ##########################
    #MHPMCOUNTER23 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hb} 
    ##########################
    #MHPMCOUNTER23 Write clear/set value 0x1f
    csrrci x14, 0xb17, 0x0
    csrrsi x14, 0xb17, 0x1f

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write clear/set value 0x0
    csrrci x14, 0xb17, 0x1f
    csrrsi x14, 0xb17, 0x0

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write clear/set value 0x15
    csrrci x14, 0xb17, 0xa
    csrrsi x14, 0xb17, 0x15

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write clear/set value 0xa
    csrrci x14, 0xb17, 0x15
    csrrsi x14, 0xb17, 0xa

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write clear/set value 0xb
    csrrci x14, 0xb17, 0x14
    csrrsi x14, 0xb17, 0xb

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    ##########################
    #MTVEC testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h5} 
    ##########################
    #MTVEC Write clear/set value 0x1f
    csrrci x14, 0x305, 0x0
    csrrsi x14, 0x305, 0x1f

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x0
    csrrci x14, 0x305, 0x1f
    csrrsi x14, 0x305, 0x0

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x15
    csrrci x14, 0x305, 0xa
    csrrsi x14, 0x305, 0x15

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write clear/set value 0xa
    csrrci x14, 0x305, 0x15
    csrrsi x14, 0x305, 0xa

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x5
    csrrci x14, 0x305, 0x1a
    csrrsi x14, 0x305, 0x5

    #MTVEC read value
    csrr x14, 0x305

    ##########################
    #MHPMCOUNTERH21 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #MHPMCOUNTERH21 Write clear/set value 0x1f
    csrrci x14, 0xb95, 0x0
    csrrsi x14, 0xb95, 0x1f

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write clear/set value 0x0
    csrrci x14, 0xb95, 0x1f
    csrrsi x14, 0xb95, 0x0

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write clear/set value 0x15
    csrrci x14, 0xb95, 0xa
    csrrsi x14, 0xb95, 0x15

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write clear/set value 0xa
    csrrci x14, 0xb95, 0x15
    csrrsi x14, 0xb95, 0xa

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write clear/set value 0x19
    csrrci x14, 0xb95, 0x6
    csrrsi x14, 0xb95, 0x19

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    ##########################
    #MHPMEVENT20 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a} 
    ##########################
    #MHPMEVENT20 Write clear/set value 0x1f
    csrrci x14, 0x334, 0x0
    csrrsi x14, 0x334, 0x1f

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write clear/set value 0x0
    csrrci x14, 0x334, 0x1f
    csrrsi x14, 0x334, 0x0

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write clear/set value 0x15
    csrrci x14, 0x334, 0xa
    csrrsi x14, 0x334, 0x15

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write clear/set value 0xa
    csrrci x14, 0x334, 0x15
    csrrsi x14, 0x334, 0xa

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write clear/set value 0x1a
    csrrci x14, 0x334, 0x5
    csrrsi x14, 0x334, 0x1a

    #MHPMEVENT20 read value
    csrr x14, 0x334

    ##########################
    #MHPMCOUNTERH18 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1c} 
    ##########################
    #MHPMCOUNTERH18 Write clear/set value 0x1f
    csrrci x14, 0xb92, 0x0
    csrrsi x14, 0xb92, 0x1f

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write clear/set value 0x0
    csrrci x14, 0xb92, 0x1f
    csrrsi x14, 0xb92, 0x0

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write clear/set value 0x15
    csrrci x14, 0xb92, 0xa
    csrrsi x14, 0xb92, 0x15

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write clear/set value 0xa
    csrrci x14, 0xb92, 0x15
    csrrsi x14, 0xb92, 0xa

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write clear/set value 0x1c
    csrrci x14, 0xb92, 0x3
    csrrsi x14, 0xb92, 0x1c

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    ##########################
    #MHPMCOUNTERH15 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4} 
    ##########################
    #MHPMCOUNTERH15 Write clear/set value 0x1f
    csrrci x14, 0xb8f, 0x0
    csrrsi x14, 0xb8f, 0x1f

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write clear/set value 0x0
    csrrci x14, 0xb8f, 0x1f
    csrrsi x14, 0xb8f, 0x0

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write clear/set value 0x15
    csrrci x14, 0xb8f, 0xa
    csrrsi x14, 0xb8f, 0x15

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write clear/set value 0xa
    csrrci x14, 0xb8f, 0x15
    csrrsi x14, 0xb8f, 0xa

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write clear/set value 0x4
    csrrci x14, 0xb8f, 0x1b
    csrrsi x14, 0xb8f, 0x4

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    ##########################
    #MHPMCOUNTERH22 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h14} 
    ##########################
    #MHPMCOUNTERH22 Write clear/set value 0x1f
    csrrci x14, 0xb96, 0x0
    csrrsi x14, 0xb96, 0x1f

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write clear/set value 0x0
    csrrci x14, 0xb96, 0x1f
    csrrsi x14, 0xb96, 0x0

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write clear/set value 0x15
    csrrci x14, 0xb96, 0xa
    csrrsi x14, 0xb96, 0x15

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write clear/set value 0xa
    csrrci x14, 0xb96, 0x15
    csrrsi x14, 0xb96, 0xa

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write clear/set value 0x14
    csrrci x14, 0xb96, 0xb
    csrrsi x14, 0xb96, 0x14

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    ##########################
    #PMPADDR11 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #PMPADDR11 Write clear/set value 0x1f
    csrrci x14, 0x3bb, 0x0
    csrrsi x14, 0x3bb, 0x1f

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write clear/set value 0x0
    csrrci x14, 0x3bb, 0x1f
    csrrsi x14, 0x3bb, 0x0

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write clear/set value 0x15
    csrrci x14, 0x3bb, 0xa
    csrrsi x14, 0x3bb, 0x15

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write clear/set value 0xa
    csrrci x14, 0x3bb, 0x15
    csrrsi x14, 0x3bb, 0xa

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write clear/set value 0xd
    csrrci x14, 0x3bb, 0x12
    csrrsi x14, 0x3bb, 0xd

    #PMPADDR11 read value
    csrr x14, 0x3bb

    ##########################
    #MHPMCOUNTERH14 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f} 
    ##########################
    #MHPMCOUNTERH14 Write clear/set value 0x1f
    csrrci x14, 0xb8e, 0x0
    csrrsi x14, 0xb8e, 0x1f

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write clear/set value 0x0
    csrrci x14, 0xb8e, 0x1f
    csrrsi x14, 0xb8e, 0x0

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write clear/set value 0x15
    csrrci x14, 0xb8e, 0xa
    csrrsi x14, 0xb8e, 0x15

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write clear/set value 0xa
    csrrci x14, 0xb8e, 0x15
    csrrsi x14, 0xb8e, 0xa

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write clear/set value 0x1f
    csrrci x14, 0xb8e, 0x0
    csrrsi x14, 0xb8e, 0x1f

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    ##########################
    #PMPADDR10 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #PMPADDR10 Write clear/set value 0x1f
    csrrci x14, 0x3ba, 0x0
    csrrsi x14, 0x3ba, 0x1f

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write clear/set value 0x0
    csrrci x14, 0x3ba, 0x1f
    csrrsi x14, 0x3ba, 0x0

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write clear/set value 0x15
    csrrci x14, 0x3ba, 0xa
    csrrsi x14, 0x3ba, 0x15

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write clear/set value 0xa
    csrrci x14, 0x3ba, 0x15
    csrrsi x14, 0x3ba, 0xa

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write clear/set value 0x10
    csrrci x14, 0x3ba, 0xf
    csrrsi x14, 0x3ba, 0x10

    #PMPADDR10 read value
    csrr x14, 0x3ba

    ##########################
    #MHPMCOUNTER27 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1d} 
    ##########################
    #MHPMCOUNTER27 Write clear/set value 0x1f
    csrrci x14, 0xb1b, 0x0
    csrrsi x14, 0xb1b, 0x1f

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write clear/set value 0x0
    csrrci x14, 0xb1b, 0x1f
    csrrsi x14, 0xb1b, 0x0

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write clear/set value 0x15
    csrrci x14, 0xb1b, 0xa
    csrrsi x14, 0xb1b, 0x15

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write clear/set value 0xa
    csrrci x14, 0xb1b, 0x15
    csrrsi x14, 0xb1b, 0xa

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write clear/set value 0x1d
    csrrci x14, 0xb1b, 0x2
    csrrsi x14, 0xb1b, 0x1d

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    ##########################
    #PMPADDR14 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h17} 
    ##########################
    #PMPADDR14 Write clear/set value 0x1f
    csrrci x14, 0x3be, 0x0
    csrrsi x14, 0x3be, 0x1f

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write clear/set value 0x0
    csrrci x14, 0x3be, 0x1f
    csrrsi x14, 0x3be, 0x0

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write clear/set value 0x15
    csrrci x14, 0x3be, 0xa
    csrrsi x14, 0x3be, 0x15

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write clear/set value 0xa
    csrrci x14, 0x3be, 0x15
    csrrsi x14, 0x3be, 0xa

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write clear/set value 0x17
    csrrci x14, 0x3be, 0x8
    csrrsi x14, 0x3be, 0x17

    #PMPADDR14 read value
    csrr x14, 0x3be

    ##########################
    #MHPMCOUNTERH26 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h17} 
    ##########################
    #MHPMCOUNTERH26 Write clear/set value 0x1f
    csrrci x14, 0xb9a, 0x0
    csrrsi x14, 0xb9a, 0x1f

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write clear/set value 0x0
    csrrci x14, 0xb9a, 0x1f
    csrrsi x14, 0xb9a, 0x0

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write clear/set value 0x15
    csrrci x14, 0xb9a, 0xa
    csrrsi x14, 0xb9a, 0x15

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write clear/set value 0xa
    csrrci x14, 0xb9a, 0x15
    csrrsi x14, 0xb9a, 0xa

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write clear/set value 0x17
    csrrci x14, 0xb9a, 0x8
    csrrsi x14, 0xb9a, 0x17

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    ##########################
    #MHPMCOUNTER14 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1b} 
    ##########################
    #MHPMCOUNTER14 Write clear/set value 0x1f
    csrrci x14, 0xb0e, 0x0
    csrrsi x14, 0xb0e, 0x1f

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write clear/set value 0x0
    csrrci x14, 0xb0e, 0x1f
    csrrsi x14, 0xb0e, 0x0

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write clear/set value 0x15
    csrrci x14, 0xb0e, 0xa
    csrrsi x14, 0xb0e, 0x15

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write clear/set value 0xa
    csrrci x14, 0xb0e, 0x15
    csrrsi x14, 0xb0e, 0xa

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write clear/set value 0x1b
    csrrci x14, 0xb0e, 0x4
    csrrsi x14, 0xb0e, 0x1b

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    ##########################
    #MHPMCOUNTERH25 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f} 
    ##########################
    #MHPMCOUNTERH25 Write clear/set value 0x1f
    csrrci x14, 0xb99, 0x0
    csrrsi x14, 0xb99, 0x1f

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write clear/set value 0x0
    csrrci x14, 0xb99, 0x1f
    csrrsi x14, 0xb99, 0x0

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write clear/set value 0x15
    csrrci x14, 0xb99, 0xa
    csrrsi x14, 0xb99, 0x15

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write clear/set value 0xa
    csrrci x14, 0xb99, 0x15
    csrrsi x14, 0xb99, 0xa

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write clear/set value 0x1f
    csrrci x14, 0xb99, 0x0
    csrrsi x14, 0xb99, 0x1f

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    ##########################
    #MHPMEVENT11 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMEVENT11 Write clear/set value 0x1f
    csrrci x14, 0x32b, 0x0
    csrrsi x14, 0x32b, 0x1f

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write clear/set value 0x0
    csrrci x14, 0x32b, 0x1f
    csrrsi x14, 0x32b, 0x0

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write clear/set value 0x15
    csrrci x14, 0x32b, 0xa
    csrrsi x14, 0x32b, 0x15

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write clear/set value 0xa
    csrrci x14, 0x32b, 0x15
    csrrsi x14, 0x32b, 0xa

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write clear/set value 0x2
    csrrci x14, 0x32b, 0x1d
    csrrsi x14, 0x32b, 0x2

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    ##########################
    #MHPMCOUNTERH23 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #MHPMCOUNTERH23 Write clear/set value 0x1f
    csrrci x14, 0xb97, 0x0
    csrrsi x14, 0xb97, 0x1f

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write clear/set value 0x0
    csrrci x14, 0xb97, 0x1f
    csrrsi x14, 0xb97, 0x0

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write clear/set value 0x15
    csrrci x14, 0xb97, 0xa
    csrrsi x14, 0xb97, 0x15

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write clear/set value 0xa
    csrrci x14, 0xb97, 0x15
    csrrsi x14, 0xb97, 0xa

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write clear/set value 0x19
    csrrci x14, 0xb97, 0x6
    csrrsi x14, 0xb97, 0x19

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    ##########################
    #MHPMCOUNTER26 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a} 
    ##########################
    #MHPMCOUNTER26 Write clear/set value 0x1f
    csrrci x14, 0xb1a, 0x0
    csrrsi x14, 0xb1a, 0x1f

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write clear/set value 0x0
    csrrci x14, 0xb1a, 0x1f
    csrrsi x14, 0xb1a, 0x0

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write clear/set value 0x15
    csrrci x14, 0xb1a, 0xa
    csrrsi x14, 0xb1a, 0x15

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write clear/set value 0xa
    csrrci x14, 0xb1a, 0x15
    csrrsi x14, 0xb1a, 0xa

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write clear/set value 0x1a
    csrrci x14, 0xb1a, 0x5
    csrrsi x14, 0xb1a, 0x1a

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    ##########################
    #MHPMCOUNTER18 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h3} 
    ##########################
    #MHPMCOUNTER18 Write clear/set value 0x1f
    csrrci x14, 0xb12, 0x0
    csrrsi x14, 0xb12, 0x1f

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write clear/set value 0x0
    csrrci x14, 0xb12, 0x1f
    csrrsi x14, 0xb12, 0x0

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write clear/set value 0x15
    csrrci x14, 0xb12, 0xa
    csrrsi x14, 0xb12, 0x15

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write clear/set value 0xa
    csrrci x14, 0xb12, 0x15
    csrrsi x14, 0xb12, 0xa

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write clear/set value 0x3
    csrrci x14, 0xb12, 0x1c
    csrrsi x14, 0xb12, 0x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    ##########################
    #MHPMCOUNTERH9 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1c} 
    ##########################
    #MHPMCOUNTERH9 Write clear/set value 0x1f
    csrrci x14, 0xb89, 0x0
    csrrsi x14, 0xb89, 0x1f

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write clear/set value 0x0
    csrrci x14, 0xb89, 0x1f
    csrrsi x14, 0xb89, 0x0

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write clear/set value 0x15
    csrrci x14, 0xb89, 0xa
    csrrsi x14, 0xb89, 0x15

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write clear/set value 0xa
    csrrci x14, 0xb89, 0x15
    csrrsi x14, 0xb89, 0xa

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write clear/set value 0x1c
    csrrci x14, 0xb89, 0x3
    csrrsi x14, 0xb89, 0x1c

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    ##########################
    #MHPMEVENT8 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMEVENT8 Write clear/set value 0x1f
    csrrci x14, 0x328, 0x0
    csrrsi x14, 0x328, 0x1f

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write clear/set value 0x0
    csrrci x14, 0x328, 0x1f
    csrrsi x14, 0x328, 0x0

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write clear/set value 0x15
    csrrci x14, 0x328, 0xa
    csrrsi x14, 0x328, 0x15

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write clear/set value 0xa
    csrrci x14, 0x328, 0x15
    csrrsi x14, 0x328, 0xa

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write clear/set value 0x2
    csrrci x14, 0x328, 0x1d
    csrrsi x14, 0x328, 0x2

    #MHPMEVENT8 read value
    csrr x14, 0x328

    ##########################
    #MHPMCOUNTER19 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f} 
    ##########################
    #MHPMCOUNTER19 Write clear/set value 0x1f
    csrrci x14, 0xb13, 0x0
    csrrsi x14, 0xb13, 0x1f

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write clear/set value 0x0
    csrrci x14, 0xb13, 0x1f
    csrrsi x14, 0xb13, 0x0

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write clear/set value 0x15
    csrrci x14, 0xb13, 0xa
    csrrsi x14, 0xb13, 0x15

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write clear/set value 0xa
    csrrci x14, 0xb13, 0x15
    csrrsi x14, 0xb13, 0xa

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write clear/set value 0x1f
    csrrci x14, 0xb13, 0x0
    csrrsi x14, 0xb13, 0x1f

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    ##########################
    #MHPMCOUNTER25 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #MHPMCOUNTER25 Write clear/set value 0x1f
    csrrci x14, 0xb19, 0x0
    csrrsi x14, 0xb19, 0x1f

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write clear/set value 0x0
    csrrci x14, 0xb19, 0x1f
    csrrsi x14, 0xb19, 0x0

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write clear/set value 0x15
    csrrci x14, 0xb19, 0xa
    csrrsi x14, 0xb19, 0x15

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write clear/set value 0xa
    csrrci x14, 0xb19, 0x15
    csrrsi x14, 0xb19, 0xa

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write clear/set value 0x18
    csrrci x14, 0xb19, 0x7
    csrrsi x14, 0xb19, 0x18

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    ##########################
    #MHPMCOUNTER29 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1d} 
    ##########################
    #MHPMCOUNTER29 Write clear/set value 0x1f
    csrrci x14, 0xb1d, 0x0
    csrrsi x14, 0xb1d, 0x1f

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write clear/set value 0x0
    csrrci x14, 0xb1d, 0x1f
    csrrsi x14, 0xb1d, 0x0

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write clear/set value 0x15
    csrrci x14, 0xb1d, 0xa
    csrrsi x14, 0xb1d, 0x15

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write clear/set value 0xa
    csrrci x14, 0xb1d, 0x15
    csrrsi x14, 0xb1d, 0xa

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write clear/set value 0x1d
    csrrci x14, 0xb1d, 0x2
    csrrsi x14, 0xb1d, 0x1d

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    ##########################
    #MEPC testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #MEPC Write clear/set value 0x1f
    csrrci x14, 0x341, 0x0
    csrrsi x14, 0x341, 0x1f

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write clear/set value 0x0
    csrrci x14, 0x341, 0x1f
    csrrsi x14, 0x341, 0x0

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write clear/set value 0x15
    csrrci x14, 0x341, 0xa
    csrrsi x14, 0x341, 0x15

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write clear/set value 0xa
    csrrci x14, 0x341, 0x15
    csrrsi x14, 0x341, 0xa

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write clear/set value 0x18
    csrrci x14, 0x341, 0x7
    csrrsi x14, 0x341, 0x18

    #MEPC read value
    csrr x14, 0x341

    ##########################
    #MHPMCOUNTER10 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #MHPMCOUNTER10 Write clear/set value 0x1f
    csrrci x14, 0xb0a, 0x0
    csrrsi x14, 0xb0a, 0x1f

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write clear/set value 0x0
    csrrci x14, 0xb0a, 0x1f
    csrrsi x14, 0xb0a, 0x0

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write clear/set value 0x15
    csrrci x14, 0xb0a, 0xa
    csrrsi x14, 0xb0a, 0x15

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write clear/set value 0xa
    csrrci x14, 0xb0a, 0x15
    csrrsi x14, 0xb0a, 0xa

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write clear/set value 0xd
    csrrci x14, 0xb0a, 0x12
    csrrsi x14, 0xb0a, 0xd

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    ##########################
    #MHPMEVENT14 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h6} 
    ##########################
    #MHPMEVENT14 Write clear/set value 0x1f
    csrrci x14, 0x32e, 0x0
    csrrsi x14, 0x32e, 0x1f

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write clear/set value 0x0
    csrrci x14, 0x32e, 0x1f
    csrrsi x14, 0x32e, 0x0

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write clear/set value 0x15
    csrrci x14, 0x32e, 0xa
    csrrsi x14, 0x32e, 0x15

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write clear/set value 0xa
    csrrci x14, 0x32e, 0x15
    csrrsi x14, 0x32e, 0xa

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write clear/set value 0x6
    csrrci x14, 0x32e, 0x19
    csrrsi x14, 0x32e, 0x6

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    ##########################
    #MHPMCOUNTERH24 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a} 
    ##########################
    #MHPMCOUNTERH24 Write clear/set value 0x1f
    csrrci x14, 0xb98, 0x0
    csrrsi x14, 0xb98, 0x1f

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write clear/set value 0x0
    csrrci x14, 0xb98, 0x1f
    csrrsi x14, 0xb98, 0x0

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write clear/set value 0x15
    csrrci x14, 0xb98, 0xa
    csrrsi x14, 0xb98, 0x15

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write clear/set value 0xa
    csrrci x14, 0xb98, 0x15
    csrrsi x14, 0xb98, 0xa

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write clear/set value 0x1a
    csrrci x14, 0xb98, 0x5
    csrrsi x14, 0xb98, 0x1a

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    ##########################
    #MHPMCOUNTER30 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #MHPMCOUNTER30 Write clear/set value 0x1f
    csrrci x14, 0xb1e, 0x0
    csrrsi x14, 0xb1e, 0x1f

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write clear/set value 0x0
    csrrci x14, 0xb1e, 0x1f
    csrrsi x14, 0xb1e, 0x0

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write clear/set value 0x15
    csrrci x14, 0xb1e, 0xa
    csrrsi x14, 0xb1e, 0x15

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write clear/set value 0xa
    csrrci x14, 0xb1e, 0x15
    csrrsi x14, 0xb1e, 0xa

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write clear/set value 0x1
    csrrci x14, 0xb1e, 0x1e
    csrrsi x14, 0xb1e, 0x1

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    ##########################
    #MCYCLEH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h13} 
    ##########################
    #MCYCLEH Write clear/set value 0x1f
    csrrci x14, 0xb80, 0x0
    csrrsi x14, 0xb80, 0x1f

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x0
    csrrci x14, 0xb80, 0x1f
    csrrsi x14, 0xb80, 0x0

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x15
    csrrci x14, 0xb80, 0xa
    csrrsi x14, 0xb80, 0x15

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0xa
    csrrci x14, 0xb80, 0x15
    csrrsi x14, 0xb80, 0xa

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x13
    csrrci x14, 0xb80, 0xc
    csrrsi x14, 0xb80, 0x13

    #MCYCLEH read value
    csrr x14, 0xb80

    ##########################
    #MHPMCOUNTERH8 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a} 
    ##########################
    #MHPMCOUNTERH8 Write clear/set value 0x1f
    csrrci x14, 0xb88, 0x0
    csrrsi x14, 0xb88, 0x1f

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write clear/set value 0x0
    csrrci x14, 0xb88, 0x1f
    csrrsi x14, 0xb88, 0x0

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write clear/set value 0x15
    csrrci x14, 0xb88, 0xa
    csrrsi x14, 0xb88, 0x15

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write clear/set value 0xa
    csrrci x14, 0xb88, 0x15
    csrrsi x14, 0xb88, 0xa

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write clear/set value 0x1a
    csrrci x14, 0xb88, 0x5
    csrrsi x14, 0xb88, 0x1a

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    ##########################
    #MIE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h14} 
    ##########################
    #MIE Write clear/set value 0x1f
    csrrci x14, 0x304, 0x0
    csrrsi x14, 0x304, 0x1f

    #MIE read value
    csrr x14, 0x304

    #MIE Write clear/set value 0x0
    csrrci x14, 0x304, 0x1f
    csrrsi x14, 0x304, 0x0

    #MIE read value
    csrr x14, 0x304

    #MIE Write clear/set value 0x15
    csrrci x14, 0x304, 0xa
    csrrsi x14, 0x304, 0x15

    #MIE read value
    csrr x14, 0x304

    #MIE Write clear/set value 0xa
    csrrci x14, 0x304, 0x15
    csrrsi x14, 0x304, 0xa

    #MIE read value
    csrr x14, 0x304

    #MIE Write clear/set value 0x14
    csrrci x14, 0x304, 0xb
    csrrsi x14, 0x304, 0x14

    #MIE read value
    csrr x14, 0x304

    ##########################
    #MHPMEVENT6 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h15} 
    ##########################
    #MHPMEVENT6 Write clear/set value 0x1f
    csrrci x14, 0x326, 0x0
    csrrsi x14, 0x326, 0x1f

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write clear/set value 0x0
    csrrci x14, 0x326, 0x1f
    csrrsi x14, 0x326, 0x0

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write clear/set value 0x15
    csrrci x14, 0x326, 0xa
    csrrsi x14, 0x326, 0x15

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write clear/set value 0xa
    csrrci x14, 0x326, 0x15
    csrrsi x14, 0x326, 0xa

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write clear/set value 0x15
    csrrci x14, 0x326, 0xa
    csrrsi x14, 0x326, 0x15

    #MHPMEVENT6 read value
    csrr x14, 0x326

    ##########################
    #MSTATUSH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16} 
    ##########################
    #MSTATUSH Write clear/set value 0x1f
    csrrci x14, 0x310, 0x0
    csrrsi x14, 0x310, 0x1f

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x0
    csrrci x14, 0x310, 0x1f
    csrrsi x14, 0x310, 0x0

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x15
    csrrci x14, 0x310, 0xa
    csrrsi x14, 0x310, 0x15

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0xa
    csrrci x14, 0x310, 0x15
    csrrsi x14, 0x310, 0xa

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x16
    csrrci x14, 0x310, 0x9
    csrrsi x14, 0x310, 0x16

    #MSTATUSH read value
    csrr x14, 0x310

    ##########################
    #MHPMCOUNTER21 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMCOUNTER21 Write clear/set value 0x1f
    csrrci x14, 0xb15, 0x0
    csrrsi x14, 0xb15, 0x1f

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write clear/set value 0x0
    csrrci x14, 0xb15, 0x1f
    csrrsi x14, 0xb15, 0x0

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write clear/set value 0x15
    csrrci x14, 0xb15, 0xa
    csrrsi x14, 0xb15, 0x15

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write clear/set value 0xa
    csrrci x14, 0xb15, 0x15
    csrrsi x14, 0xb15, 0xa

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write clear/set value 0x2
    csrrci x14, 0xb15, 0x1d
    csrrsi x14, 0xb15, 0x2

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    ##########################
    #MHPMEVENT25 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h3} 
    ##########################
    #MHPMEVENT25 Write clear/set value 0x1f
    csrrci x14, 0x339, 0x0
    csrrsi x14, 0x339, 0x1f

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write clear/set value 0x0
    csrrci x14, 0x339, 0x1f
    csrrsi x14, 0x339, 0x0

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write clear/set value 0x15
    csrrci x14, 0x339, 0xa
    csrrsi x14, 0x339, 0x15

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write clear/set value 0xa
    csrrci x14, 0x339, 0x15
    csrrsi x14, 0x339, 0xa

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write clear/set value 0x3
    csrrci x14, 0x339, 0x1c
    csrrsi x14, 0x339, 0x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    ##########################
    #MHPMEVENT21 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMEVENT21 Write clear/set value 0x1f
    csrrci x14, 0x335, 0x0
    csrrsi x14, 0x335, 0x1f

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write clear/set value 0x0
    csrrci x14, 0x335, 0x1f
    csrrsi x14, 0x335, 0x0

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write clear/set value 0x15
    csrrci x14, 0x335, 0xa
    csrrsi x14, 0x335, 0x15

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write clear/set value 0xa
    csrrci x14, 0x335, 0x15
    csrrsi x14, 0x335, 0xa

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write clear/set value 0x2
    csrrci x14, 0x335, 0x1d
    csrrsi x14, 0x335, 0x2

    #MHPMEVENT21 read value
    csrr x14, 0x335

    ##########################
    #PMPCFG3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h12} 
    ##########################
    #PMPCFG3 Write clear/set value 0x1f
    csrrci x14, 0x3a3, 0x0
    csrrsi x14, 0x3a3, 0x1f

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write clear/set value 0x0
    csrrci x14, 0x3a3, 0x1f
    csrrsi x14, 0x3a3, 0x0

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write clear/set value 0x15
    csrrci x14, 0x3a3, 0xa
    csrrsi x14, 0x3a3, 0x15

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write clear/set value 0xa
    csrrci x14, 0x3a3, 0x15
    csrrsi x14, 0x3a3, 0xa

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write clear/set value 0x12
    csrrci x14, 0x3a3, 0xd
    csrrsi x14, 0x3a3, 0x12

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #INSTRETH WR skipped since it's a RO register

    ##########################
    #MHPMEVENT17 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #MHPMEVENT17 Write clear/set value 0x1f
    csrrci x14, 0x331, 0x0
    csrrsi x14, 0x331, 0x1f

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write clear/set value 0x0
    csrrci x14, 0x331, 0x1f
    csrrsi x14, 0x331, 0x0

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write clear/set value 0x15
    csrrci x14, 0x331, 0xa
    csrrsi x14, 0x331, 0x15

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write clear/set value 0xa
    csrrci x14, 0x331, 0x15
    csrrsi x14, 0x331, 0xa

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write clear/set value 0x1
    csrrci x14, 0x331, 0x1e
    csrrsi x14, 0x331, 0x1

    #MHPMEVENT17 read value
    csrr x14, 0x331

    ##########################
    #MHPMCOUNTER24 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMCOUNTER24 Write clear/set value 0x1f
    csrrci x14, 0xb18, 0x0
    csrrsi x14, 0xb18, 0x1f

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write clear/set value 0x0
    csrrci x14, 0xb18, 0x1f
    csrrsi x14, 0xb18, 0x0

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write clear/set value 0x15
    csrrci x14, 0xb18, 0xa
    csrrsi x14, 0xb18, 0x15

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write clear/set value 0xa
    csrrci x14, 0xb18, 0x15
    csrrsi x14, 0xb18, 0xa

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write clear/set value 0x2
    csrrci x14, 0xb18, 0x1d
    csrrsi x14, 0xb18, 0x2

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    ##########################
    #MISA testing W/R values '{'h1b, 'h4, 'h15, 'ha, 'h13} 
    ##########################
    #MISA Write clear/set value 0x1b
    csrrci x14, 0x301, 0x4
    csrrsi x14, 0x301, 0x1b

    #MISA read value
    csrr x14, 0x301

    #MISA Write clear/set value 0x4
    csrrci x14, 0x301, 0x1b
    csrrsi x14, 0x301, 0x4

    #MISA read value
    csrr x14, 0x301

    #MISA Write clear/set value 0x15
    csrrci x14, 0x301, 0xa
    csrrsi x14, 0x301, 0x15

    #MISA read value
    csrr x14, 0x301

    #MISA Write clear/set value 0xa
    csrrci x14, 0x301, 0x15
    csrrsi x14, 0x301, 0xa

    #MISA read value
    csrr x14, 0x301

    #MISA Write clear/set value 0x13
    csrrci x14, 0x301, 0xc
    csrrsi x14, 0x301, 0x13

    #MISA read value
    csrr x14, 0x301

    ##########################
    #MHPMEVENT5 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h15} 
    ##########################
    #MHPMEVENT5 Write clear/set value 0x1f
    csrrci x14, 0x325, 0x0
    csrrsi x14, 0x325, 0x1f

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write clear/set value 0x0
    csrrci x14, 0x325, 0x1f
    csrrsi x14, 0x325, 0x0

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write clear/set value 0x15
    csrrci x14, 0x325, 0xa
    csrrsi x14, 0x325, 0x15

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write clear/set value 0xa
    csrrci x14, 0x325, 0x15
    csrrsi x14, 0x325, 0xa

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write clear/set value 0x15
    csrrci x14, 0x325, 0xa
    csrrsi x14, 0x325, 0x15

    #MHPMEVENT5 read value
    csrr x14, 0x325

    ##########################
    #MHPMEVENT29 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #MHPMEVENT29 Write clear/set value 0x1f
    csrrci x14, 0x33d, 0x0
    csrrsi x14, 0x33d, 0x1f

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write clear/set value 0x0
    csrrci x14, 0x33d, 0x1f
    csrrsi x14, 0x33d, 0x0

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write clear/set value 0x15
    csrrci x14, 0x33d, 0xa
    csrrsi x14, 0x33d, 0x15

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write clear/set value 0xa
    csrrci x14, 0x33d, 0x15
    csrrsi x14, 0x33d, 0xa

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write clear/set value 0xd
    csrrci x14, 0x33d, 0x12
    csrrsi x14, 0x33d, 0xd

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    ##########################
    #MHPMCOUNTERH4 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #MHPMCOUNTERH4 Write clear/set value 0x1f
    csrrci x14, 0xb84, 0x0
    csrrsi x14, 0xb84, 0x1f

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write clear/set value 0x0
    csrrci x14, 0xb84, 0x1f
    csrrsi x14, 0xb84, 0x0

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write clear/set value 0x15
    csrrci x14, 0xb84, 0xa
    csrrsi x14, 0xb84, 0x15

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write clear/set value 0xa
    csrrci x14, 0xb84, 0x15
    csrrsi x14, 0xb84, 0xa

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write clear/set value 0xd
    csrrci x14, 0xb84, 0x12
    csrrsi x14, 0xb84, 0xd

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #INSTRET WR skipped since it's a RO register

    ##########################
    #PMPADDR9 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h3} 
    ##########################
    #PMPADDR9 Write clear/set value 0x1f
    csrrci x14, 0x3b9, 0x0
    csrrsi x14, 0x3b9, 0x1f

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write clear/set value 0x0
    csrrci x14, 0x3b9, 0x1f
    csrrsi x14, 0x3b9, 0x0

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write clear/set value 0x15
    csrrci x14, 0x3b9, 0xa
    csrrsi x14, 0x3b9, 0x15

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write clear/set value 0xa
    csrrci x14, 0x3b9, 0x15
    csrrsi x14, 0x3b9, 0xa

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write clear/set value 0x3
    csrrci x14, 0x3b9, 0x1c
    csrrsi x14, 0x3b9, 0x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    ##########################
    #MHPMCOUNTERH5 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f} 
    ##########################
    #MHPMCOUNTERH5 Write clear/set value 0x1f
    csrrci x14, 0xb85, 0x0
    csrrsi x14, 0xb85, 0x1f

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write clear/set value 0x0
    csrrci x14, 0xb85, 0x1f
    csrrsi x14, 0xb85, 0x0

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write clear/set value 0x15
    csrrci x14, 0xb85, 0xa
    csrrsi x14, 0xb85, 0x15

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write clear/set value 0xa
    csrrci x14, 0xb85, 0x15
    csrrsi x14, 0xb85, 0xa

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write clear/set value 0x1f
    csrrci x14, 0xb85, 0x0
    csrrsi x14, 0xb85, 0x1f

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    ##########################
    #MHPMCOUNTER4 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hc} 
    ##########################
    #MHPMCOUNTER4 Write clear/set value 0x1f
    csrrci x14, 0xb04, 0x0
    csrrsi x14, 0xb04, 0x1f

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write clear/set value 0x0
    csrrci x14, 0xb04, 0x1f
    csrrsi x14, 0xb04, 0x0

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write clear/set value 0x15
    csrrci x14, 0xb04, 0xa
    csrrsi x14, 0xb04, 0x15

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write clear/set value 0xa
    csrrci x14, 0xb04, 0x15
    csrrsi x14, 0xb04, 0xa

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write clear/set value 0xc
    csrrci x14, 0xb04, 0x13
    csrrsi x14, 0xb04, 0xc

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MIMPID WR skipped since it's a RO register

    ##########################
    #MHPMEVENT10 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h9} 
    ##########################
    #MHPMEVENT10 Write clear/set value 0x1f
    csrrci x14, 0x32a, 0x0
    csrrsi x14, 0x32a, 0x1f

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write clear/set value 0x0
    csrrci x14, 0x32a, 0x1f
    csrrsi x14, 0x32a, 0x0

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write clear/set value 0x15
    csrrci x14, 0x32a, 0xa
    csrrsi x14, 0x32a, 0x15

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write clear/set value 0xa
    csrrci x14, 0x32a, 0x15
    csrrsi x14, 0x32a, 0xa

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write clear/set value 0x9
    csrrci x14, 0x32a, 0x16
    csrrsi x14, 0x32a, 0x9

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    ##########################
    #MHPMCOUNTERH20 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1d} 
    ##########################
    #MHPMCOUNTERH20 Write clear/set value 0x1f
    csrrci x14, 0xb94, 0x0
    csrrsi x14, 0xb94, 0x1f

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write clear/set value 0x0
    csrrci x14, 0xb94, 0x1f
    csrrsi x14, 0xb94, 0x0

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write clear/set value 0x15
    csrrci x14, 0xb94, 0xa
    csrrsi x14, 0xb94, 0x15

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write clear/set value 0xa
    csrrci x14, 0xb94, 0x15
    csrrsi x14, 0xb94, 0xa

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write clear/set value 0x1d
    csrrci x14, 0xb94, 0x2
    csrrsi x14, 0xb94, 0x1d

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    ##########################
    #MHPMEVENT7 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h17} 
    ##########################
    #MHPMEVENT7 Write clear/set value 0x1f
    csrrci x14, 0x327, 0x0
    csrrsi x14, 0x327, 0x1f

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write clear/set value 0x0
    csrrci x14, 0x327, 0x1f
    csrrsi x14, 0x327, 0x0

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write clear/set value 0x15
    csrrci x14, 0x327, 0xa
    csrrsi x14, 0x327, 0x15

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write clear/set value 0xa
    csrrci x14, 0x327, 0x15
    csrrsi x14, 0x327, 0xa

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write clear/set value 0x17
    csrrci x14, 0x327, 0x8
    csrrsi x14, 0x327, 0x17

    #MHPMEVENT7 read value
    csrr x14, 0x327

    ##########################
    #MHPMCOUNTER11 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h11} 
    ##########################
    #MHPMCOUNTER11 Write clear/set value 0x1f
    csrrci x14, 0xb0b, 0x0
    csrrsi x14, 0xb0b, 0x1f

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write clear/set value 0x0
    csrrci x14, 0xb0b, 0x1f
    csrrsi x14, 0xb0b, 0x0

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write clear/set value 0x15
    csrrci x14, 0xb0b, 0xa
    csrrsi x14, 0xb0b, 0x15

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write clear/set value 0xa
    csrrci x14, 0xb0b, 0x15
    csrrsi x14, 0xb0b, 0xa

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write clear/set value 0x11
    csrrci x14, 0xb0b, 0xe
    csrrsi x14, 0xb0b, 0x11

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    ##########################
    #MHPMEVENT3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hf} 
    ##########################
    #MHPMEVENT3 Write clear/set value 0x1f
    csrrci x14, 0x323, 0x0
    csrrsi x14, 0x323, 0x1f

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write clear/set value 0x0
    csrrci x14, 0x323, 0x1f
    csrrsi x14, 0x323, 0x0

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write clear/set value 0x15
    csrrci x14, 0x323, 0xa
    csrrsi x14, 0x323, 0x15

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write clear/set value 0xa
    csrrci x14, 0x323, 0x15
    csrrsi x14, 0x323, 0xa

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write clear/set value 0xf
    csrrci x14, 0x323, 0x10
    csrrsi x14, 0x323, 0xf

    #MHPMEVENT3 read value
    csrr x14, 0x323

    ##########################
    #MHPMCOUNTERH31 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'he} 
    ##########################
    #MHPMCOUNTERH31 Write clear/set value 0x1f
    csrrci x14, 0xb9f, 0x0
    csrrsi x14, 0xb9f, 0x1f

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write clear/set value 0x0
    csrrci x14, 0xb9f, 0x1f
    csrrsi x14, 0xb9f, 0x0

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write clear/set value 0x15
    csrrci x14, 0xb9f, 0xa
    csrrsi x14, 0xb9f, 0x15

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write clear/set value 0xa
    csrrci x14, 0xb9f, 0x15
    csrrsi x14, 0xb9f, 0xa

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write clear/set value 0xe
    csrrci x14, 0xb9f, 0x11
    csrrsi x14, 0xb9f, 0xe

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #CYCLE WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTER6 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h6} 
    ##########################
    #MHPMCOUNTER6 Write clear/set value 0x1f
    csrrci x14, 0xb06, 0x0
    csrrsi x14, 0xb06, 0x1f

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write clear/set value 0x0
    csrrci x14, 0xb06, 0x1f
    csrrsi x14, 0xb06, 0x0

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write clear/set value 0x15
    csrrci x14, 0xb06, 0xa
    csrrsi x14, 0xb06, 0x15

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write clear/set value 0xa
    csrrci x14, 0xb06, 0x15
    csrrsi x14, 0xb06, 0xa

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write clear/set value 0x6
    csrrci x14, 0xb06, 0x19
    csrrsi x14, 0xb06, 0x6

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    ##########################
    #MHPMCOUNTER13 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h13} 
    ##########################
    #MHPMCOUNTER13 Write clear/set value 0x1f
    csrrci x14, 0xb0d, 0x0
    csrrsi x14, 0xb0d, 0x1f

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write clear/set value 0x0
    csrrci x14, 0xb0d, 0x1f
    csrrsi x14, 0xb0d, 0x0

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write clear/set value 0x15
    csrrci x14, 0xb0d, 0xa
    csrrsi x14, 0xb0d, 0x15

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write clear/set value 0xa
    csrrci x14, 0xb0d, 0x15
    csrrsi x14, 0xb0d, 0xa

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write clear/set value 0x13
    csrrci x14, 0xb0d, 0xc
    csrrsi x14, 0xb0d, 0x13

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    ##########################
    #MINSTRETH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16} 
    ##########################
    #MINSTRETH Write clear/set value 0x1f
    csrrci x14, 0xb82, 0x0
    csrrsi x14, 0xb82, 0x1f

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x0
    csrrci x14, 0xb82, 0x1f
    csrrsi x14, 0xb82, 0x0

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x15
    csrrci x14, 0xb82, 0xa
    csrrsi x14, 0xb82, 0x15

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0xa
    csrrci x14, 0xb82, 0x15
    csrrsi x14, 0xb82, 0xa

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x16
    csrrci x14, 0xb82, 0x9
    csrrsi x14, 0xb82, 0x16

    #MINSTRETH read value
    csrr x14, 0xb82

    ##########################
    #PMPADDR0 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #PMPADDR0 Write clear/set value 0x1f
    csrrci x14, 0x3b0, 0x0
    csrrsi x14, 0x3b0, 0x1f

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write clear/set value 0x0
    csrrci x14, 0x3b0, 0x1f
    csrrsi x14, 0x3b0, 0x0

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write clear/set value 0x15
    csrrci x14, 0x3b0, 0xa
    csrrsi x14, 0x3b0, 0x15

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write clear/set value 0xa
    csrrci x14, 0x3b0, 0x15
    csrrsi x14, 0x3b0, 0xa

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write clear/set value 0x10
    csrrci x14, 0x3b0, 0xf
    csrrsi x14, 0x3b0, 0x10

    #PMPADDR0 read value
    csrr x14, 0x3b0

    ##########################
    #MHPMCOUNTER31 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h3} 
    ##########################
    #MHPMCOUNTER31 Write clear/set value 0x1f
    csrrci x14, 0xb1f, 0x0
    csrrsi x14, 0xb1f, 0x1f

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write clear/set value 0x0
    csrrci x14, 0xb1f, 0x1f
    csrrsi x14, 0xb1f, 0x0

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write clear/set value 0x15
    csrrci x14, 0xb1f, 0xa
    csrrsi x14, 0xb1f, 0x15

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write clear/set value 0xa
    csrrci x14, 0xb1f, 0x15
    csrrsi x14, 0xb1f, 0xa

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write clear/set value 0x3
    csrrci x14, 0xb1f, 0x1c
    csrrsi x14, 0xb1f, 0x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    ##########################
    #PMPADDR3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'he} 
    ##########################
    #PMPADDR3 Write clear/set value 0x1f
    csrrci x14, 0x3b3, 0x0
    csrrsi x14, 0x3b3, 0x1f

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write clear/set value 0x0
    csrrci x14, 0x3b3, 0x1f
    csrrsi x14, 0x3b3, 0x0

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write clear/set value 0x15
    csrrci x14, 0x3b3, 0xa
    csrrsi x14, 0x3b3, 0x15

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write clear/set value 0xa
    csrrci x14, 0x3b3, 0x15
    csrrsi x14, 0x3b3, 0xa

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write clear/set value 0xe
    csrrci x14, 0x3b3, 0x11
    csrrsi x14, 0x3b3, 0xe

    #PMPADDR3 read value
    csrr x14, 0x3b3

    ##########################
    #MINSTRET testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1e} 
    ##########################
    #MINSTRET Write clear/set value 0x1f
    csrrci x14, 0xb02, 0x0
    csrrsi x14, 0xb02, 0x1f

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x0
    csrrci x14, 0xb02, 0x1f
    csrrsi x14, 0xb02, 0x0

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x15
    csrrci x14, 0xb02, 0xa
    csrrsi x14, 0xb02, 0x15

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0xa
    csrrci x14, 0xb02, 0x15
    csrrsi x14, 0xb02, 0xa

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x1e
    csrrci x14, 0xb02, 0x1
    csrrsi x14, 0xb02, 0x1e

    #MINSTRET read value
    csrr x14, 0xb02

    #CYCLEH WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTER17 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4} 
    ##########################
    #MHPMCOUNTER17 Write clear/set value 0x1f
    csrrci x14, 0xb11, 0x0
    csrrsi x14, 0xb11, 0x1f

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write clear/set value 0x0
    csrrci x14, 0xb11, 0x1f
    csrrsi x14, 0xb11, 0x0

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write clear/set value 0x15
    csrrci x14, 0xb11, 0xa
    csrrsi x14, 0xb11, 0x15

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write clear/set value 0xa
    csrrci x14, 0xb11, 0x15
    csrrsi x14, 0xb11, 0xa

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write clear/set value 0x4
    csrrci x14, 0xb11, 0x1b
    csrrsi x14, 0xb11, 0x4

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    ##########################
    #MHPMCOUNTERH6 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h8} 
    ##########################
    #MHPMCOUNTERH6 Write clear/set value 0x1f
    csrrci x14, 0xb86, 0x0
    csrrsi x14, 0xb86, 0x1f

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write clear/set value 0x0
    csrrci x14, 0xb86, 0x1f
    csrrsi x14, 0xb86, 0x0

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write clear/set value 0x15
    csrrci x14, 0xb86, 0xa
    csrrsi x14, 0xb86, 0x15

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write clear/set value 0xa
    csrrci x14, 0xb86, 0x15
    csrrsi x14, 0xb86, 0xa

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write clear/set value 0x8
    csrrci x14, 0xb86, 0x17
    csrrsi x14, 0xb86, 0x8

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    ##########################
    #MHPMEVENT31 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h6} 
    ##########################
    #MHPMEVENT31 Write clear/set value 0x1f
    csrrci x14, 0x33f, 0x0
    csrrsi x14, 0x33f, 0x1f

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write clear/set value 0x0
    csrrci x14, 0x33f, 0x1f
    csrrsi x14, 0x33f, 0x0

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write clear/set value 0x15
    csrrci x14, 0x33f, 0xa
    csrrsi x14, 0x33f, 0x15

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write clear/set value 0xa
    csrrci x14, 0x33f, 0x15
    csrrsi x14, 0x33f, 0xa

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write clear/set value 0x6
    csrrci x14, 0x33f, 0x19
    csrrsi x14, 0x33f, 0x6

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    ##########################
    #PMPCFG2 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'ha} 
    ##########################
    #PMPCFG2 Write clear/set value 0x1f
    csrrci x14, 0x3a2, 0x0
    csrrsi x14, 0x3a2, 0x1f

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write clear/set value 0x0
    csrrci x14, 0x3a2, 0x1f
    csrrsi x14, 0x3a2, 0x0

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write clear/set value 0x15
    csrrci x14, 0x3a2, 0xa
    csrrsi x14, 0x3a2, 0x15

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write clear/set value 0xa
    csrrci x14, 0x3a2, 0x15
    csrrsi x14, 0x3a2, 0xa

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write clear/set value 0xa
    csrrci x14, 0x3a2, 0x15
    csrrsi x14, 0x3a2, 0xa

    #PMPCFG2 read value
    csrr x14, 0x3a2

    ##########################
    #MHPMCOUNTERH10 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h17} 
    ##########################
    #MHPMCOUNTERH10 Write clear/set value 0x1f
    csrrci x14, 0xb8a, 0x0
    csrrsi x14, 0xb8a, 0x1f

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write clear/set value 0x0
    csrrci x14, 0xb8a, 0x1f
    csrrsi x14, 0xb8a, 0x0

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write clear/set value 0x15
    csrrci x14, 0xb8a, 0xa
    csrrsi x14, 0xb8a, 0x15

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write clear/set value 0xa
    csrrci x14, 0xb8a, 0x15
    csrrsi x14, 0xb8a, 0xa

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write clear/set value 0x17
    csrrci x14, 0xb8a, 0x8
    csrrsi x14, 0xb8a, 0x17

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    ##########################
    #PMPADDR12 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'ha} 
    ##########################
    #PMPADDR12 Write clear/set value 0x1f
    csrrci x14, 0x3bc, 0x0
    csrrsi x14, 0x3bc, 0x1f

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write clear/set value 0x0
    csrrci x14, 0x3bc, 0x1f
    csrrsi x14, 0x3bc, 0x0

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write clear/set value 0x15
    csrrci x14, 0x3bc, 0xa
    csrrsi x14, 0x3bc, 0x15

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write clear/set value 0xa
    csrrci x14, 0x3bc, 0x15
    csrrsi x14, 0x3bc, 0xa

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write clear/set value 0xa
    csrrci x14, 0x3bc, 0x15
    csrrsi x14, 0x3bc, 0xa

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #MARCHID WR skipped since it's a RO register

    ##########################
    #PMPADDR15 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h17} 
    ##########################
    #PMPADDR15 Write clear/set value 0x1f
    csrrci x14, 0x3bf, 0x0
    csrrsi x14, 0x3bf, 0x1f

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write clear/set value 0x0
    csrrci x14, 0x3bf, 0x1f
    csrrsi x14, 0x3bf, 0x0

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write clear/set value 0x15
    csrrci x14, 0x3bf, 0xa
    csrrsi x14, 0x3bf, 0x15

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write clear/set value 0xa
    csrrci x14, 0x3bf, 0x15
    csrrsi x14, 0x3bf, 0xa

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write clear/set value 0x17
    csrrci x14, 0x3bf, 0x8
    csrrsi x14, 0x3bf, 0x17

    #PMPADDR15 read value
    csrr x14, 0x3bf

    ##########################
    #MHPMEVENT13 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7} 
    ##########################
    #MHPMEVENT13 Write clear/set value 0x1f
    csrrci x14, 0x32d, 0x0
    csrrsi x14, 0x32d, 0x1f

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write clear/set value 0x0
    csrrci x14, 0x32d, 0x1f
    csrrsi x14, 0x32d, 0x0

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write clear/set value 0x15
    csrrci x14, 0x32d, 0xa
    csrrsi x14, 0x32d, 0x15

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write clear/set value 0xa
    csrrci x14, 0x32d, 0x15
    csrrsi x14, 0x32d, 0xa

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write clear/set value 0x7
    csrrci x14, 0x32d, 0x18
    csrrsi x14, 0x32d, 0x7

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    ##########################
    #MHPMCOUNTER7 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMCOUNTER7 Write clear/set value 0x1f
    csrrci x14, 0xb07, 0x0
    csrrsi x14, 0xb07, 0x1f

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write clear/set value 0x0
    csrrci x14, 0xb07, 0x1f
    csrrsi x14, 0xb07, 0x0

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write clear/set value 0x15
    csrrci x14, 0xb07, 0xa
    csrrsi x14, 0xb07, 0x15

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write clear/set value 0xa
    csrrci x14, 0xb07, 0x15
    csrrsi x14, 0xb07, 0xa

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write clear/set value 0x2
    csrrci x14, 0xb07, 0x1d
    csrrsi x14, 0xb07, 0x2

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    ##########################
    #MHPMCOUNTERH3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #MHPMCOUNTERH3 Write clear/set value 0x1f
    csrrci x14, 0xb83, 0x0
    csrrsi x14, 0xb83, 0x1f

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write clear/set value 0x0
    csrrci x14, 0xb83, 0x1f
    csrrsi x14, 0xb83, 0x0

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write clear/set value 0x15
    csrrci x14, 0xb83, 0xa
    csrrsi x14, 0xb83, 0x15

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write clear/set value 0xa
    csrrci x14, 0xb83, 0x15
    csrrsi x14, 0xb83, 0xa

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write clear/set value 0x10
    csrrci x14, 0xb83, 0xf
    csrrsi x14, 0xb83, 0x10

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    ##########################
    #MHPMCOUNTER3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hc} 
    ##########################
    #MHPMCOUNTER3 Write clear/set value 0x1f
    csrrci x14, 0xb03, 0x0
    csrrsi x14, 0xb03, 0x1f

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write clear/set value 0x0
    csrrci x14, 0xb03, 0x1f
    csrrsi x14, 0xb03, 0x0

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write clear/set value 0x15
    csrrci x14, 0xb03, 0xa
    csrrsi x14, 0xb03, 0x15

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write clear/set value 0xa
    csrrci x14, 0xb03, 0x15
    csrrsi x14, 0xb03, 0xa

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write clear/set value 0xc
    csrrci x14, 0xb03, 0x13
    csrrsi x14, 0xb03, 0xc

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    ##########################
    #MHPMCOUNTER15 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h0} 
    ##########################
    #MHPMCOUNTER15 Write clear/set value 0x1f
    csrrci x14, 0xb0f, 0x0
    csrrsi x14, 0xb0f, 0x1f

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write clear/set value 0x0
    csrrci x14, 0xb0f, 0x1f
    csrrsi x14, 0xb0f, 0x0

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write clear/set value 0x15
    csrrci x14, 0xb0f, 0xa
    csrrsi x14, 0xb0f, 0x15

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write clear/set value 0xa
    csrrci x14, 0xb0f, 0x15
    csrrsi x14, 0xb0f, 0xa

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write clear/set value 0x0
    csrrci x14, 0xb0f, 0x1f
    csrrsi x14, 0xb0f, 0x0

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    ##########################
    #PMPCFG1 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4} 
    ##########################
    #PMPCFG1 Write clear/set value 0x1f
    csrrci x14, 0x3a1, 0x0
    csrrsi x14, 0x3a1, 0x1f

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write clear/set value 0x0
    csrrci x14, 0x3a1, 0x1f
    csrrsi x14, 0x3a1, 0x0

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write clear/set value 0x15
    csrrci x14, 0x3a1, 0xa
    csrrsi x14, 0x3a1, 0x15

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write clear/set value 0xa
    csrrci x14, 0x3a1, 0x15
    csrrsi x14, 0x3a1, 0xa

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write clear/set value 0x4
    csrrci x14, 0x3a1, 0x1b
    csrrsi x14, 0x3a1, 0x4

    #PMPCFG1 read value
    csrr x14, 0x3a1

    ##########################
    #MHPMEVENT19 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'he} 
    ##########################
    #MHPMEVENT19 Write clear/set value 0x1f
    csrrci x14, 0x333, 0x0
    csrrsi x14, 0x333, 0x1f

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write clear/set value 0x0
    csrrci x14, 0x333, 0x1f
    csrrsi x14, 0x333, 0x0

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write clear/set value 0x15
    csrrci x14, 0x333, 0xa
    csrrsi x14, 0x333, 0x15

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write clear/set value 0xa
    csrrci x14, 0x333, 0x15
    csrrsi x14, 0x333, 0xa

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write clear/set value 0xe
    csrrci x14, 0x333, 0x11
    csrrsi x14, 0x333, 0xe

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHARTID WR skipped since it's a RO register

    ##########################
    #PMPADDR1 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h15} 
    ##########################
    #PMPADDR1 Write clear/set value 0x1f
    csrrci x14, 0x3b1, 0x0
    csrrsi x14, 0x3b1, 0x1f

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write clear/set value 0x0
    csrrci x14, 0x3b1, 0x1f
    csrrsi x14, 0x3b1, 0x0

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write clear/set value 0x15
    csrrci x14, 0x3b1, 0xa
    csrrsi x14, 0x3b1, 0x15

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write clear/set value 0xa
    csrrci x14, 0x3b1, 0x15
    csrrsi x14, 0x3b1, 0xa

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write clear/set value 0x15
    csrrci x14, 0x3b1, 0xa
    csrrsi x14, 0x3b1, 0x15

    #PMPADDR1 read value
    csrr x14, 0x3b1

    ##########################
    #MHPMEVENT22 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #MHPMEVENT22 Write clear/set value 0x1f
    csrrci x14, 0x336, 0x0
    csrrsi x14, 0x336, 0x1f

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write clear/set value 0x0
    csrrci x14, 0x336, 0x1f
    csrrsi x14, 0x336, 0x0

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write clear/set value 0x15
    csrrci x14, 0x336, 0xa
    csrrsi x14, 0x336, 0x15

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write clear/set value 0xa
    csrrci x14, 0x336, 0x15
    csrrsi x14, 0x336, 0xa

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write clear/set value 0x10
    csrrci x14, 0x336, 0xf
    csrrsi x14, 0x336, 0x10

    #MHPMEVENT22 read value
    csrr x14, 0x336

    ##########################
    #ICACHE testing W/R values '{'h1e, 'h1, 'h15, 'ha, 'h1d} 
    ##########################
    #ICACHE Write clear/set value 0x1e
    csrrci x14, 0x7c0, 0x1
    csrrsi x14, 0x7c0, 0x1e

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write clear/set value 0x1
    csrrci x14, 0x7c0, 0x1e
    csrrsi x14, 0x7c0, 0x1

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write clear/set value 0x15
    csrrci x14, 0x7c0, 0xa
    csrrsi x14, 0x7c0, 0x15

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write clear/set value 0xa
    csrrci x14, 0x7c0, 0x15
    csrrsi x14, 0x7c0, 0xa

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write clear/set value 0x1d
    csrrci x14, 0x7c0, 0x2
    csrrsi x14, 0x7c0, 0x1d

    #ICACHE read value
    csrr x14, 0x7c0

    #MVENDORID WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTERH13 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #MHPMCOUNTERH13 Write clear/set value 0x1f
    csrrci x14, 0xb8d, 0x0
    csrrsi x14, 0xb8d, 0x1f

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write clear/set value 0x0
    csrrci x14, 0xb8d, 0x1f
    csrrsi x14, 0xb8d, 0x0

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write clear/set value 0x15
    csrrci x14, 0xb8d, 0xa
    csrrsi x14, 0xb8d, 0x15

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write clear/set value 0xa
    csrrci x14, 0xb8d, 0x15
    csrrsi x14, 0xb8d, 0xa

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write clear/set value 0xd
    csrrci x14, 0xb8d, 0x12
    csrrsi x14, 0xb8d, 0xd

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    ##########################
    #MHPMCOUNTERH29 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h17} 
    ##########################
    #MHPMCOUNTERH29 Write clear/set value 0x1f
    csrrci x14, 0xb9d, 0x0
    csrrsi x14, 0xb9d, 0x1f

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write clear/set value 0x0
    csrrci x14, 0xb9d, 0x1f
    csrrsi x14, 0xb9d, 0x0

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write clear/set value 0x15
    csrrci x14, 0xb9d, 0xa
    csrrsi x14, 0xb9d, 0x15

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write clear/set value 0xa
    csrrci x14, 0xb9d, 0x15
    csrrsi x14, 0xb9d, 0xa

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write clear/set value 0x17
    csrrci x14, 0xb9d, 0x8
    csrrsi x14, 0xb9d, 0x17

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    ##########################
    #MHPMEVENT28 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h15} 
    ##########################
    #MHPMEVENT28 Write clear/set value 0x1f
    csrrci x14, 0x33c, 0x0
    csrrsi x14, 0x33c, 0x1f

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write clear/set value 0x0
    csrrci x14, 0x33c, 0x1f
    csrrsi x14, 0x33c, 0x0

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write clear/set value 0x15
    csrrci x14, 0x33c, 0xa
    csrrsi x14, 0x33c, 0x15

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write clear/set value 0xa
    csrrci x14, 0x33c, 0x15
    csrrsi x14, 0x33c, 0xa

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write clear/set value 0x15
    csrrci x14, 0x33c, 0xa
    csrrsi x14, 0x33c, 0x15

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    ##########################
    #MHPMCOUNTER20 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'he} 
    ##########################
    #MHPMCOUNTER20 Write clear/set value 0x1f
    csrrci x14, 0xb14, 0x0
    csrrsi x14, 0xb14, 0x1f

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write clear/set value 0x0
    csrrci x14, 0xb14, 0x1f
    csrrsi x14, 0xb14, 0x0

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write clear/set value 0x15
    csrrci x14, 0xb14, 0xa
    csrrsi x14, 0xb14, 0x15

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write clear/set value 0xa
    csrrci x14, 0xb14, 0x15
    csrrsi x14, 0xb14, 0xa

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write clear/set value 0xe
    csrrci x14, 0xb14, 0x11
    csrrsi x14, 0xb14, 0xe

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    ##########################
    #MHPMCOUNTER5 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #MHPMCOUNTER5 Write clear/set value 0x1f
    csrrci x14, 0xb05, 0x0
    csrrsi x14, 0xb05, 0x1f

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write clear/set value 0x0
    csrrci x14, 0xb05, 0x1f
    csrrsi x14, 0xb05, 0x0

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write clear/set value 0x15
    csrrci x14, 0xb05, 0xa
    csrrsi x14, 0xb05, 0x15

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write clear/set value 0xa
    csrrci x14, 0xb05, 0x15
    csrrsi x14, 0xb05, 0xa

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write clear/set value 0x19
    csrrci x14, 0xb05, 0x6
    csrrsi x14, 0xb05, 0x19

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    ##########################
    #MSTATUS testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f} 
    ##########################
    #MSTATUS Write clear/set value 0x1f
    csrrci x14, 0x300, 0x0
    csrrsi x14, 0x300, 0x1f

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x0
    csrrci x14, 0x300, 0x1f
    csrrsi x14, 0x300, 0x0

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x15
    csrrci x14, 0x300, 0xa
    csrrsi x14, 0x300, 0x15

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0xa
    csrrci x14, 0x300, 0x15
    csrrsi x14, 0x300, 0xa

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x1f
    csrrci x14, 0x300, 0x0
    csrrsi x14, 0x300, 0x1f

    #MSTATUS read value
    csrr x14, 0x300

    ##########################
    #MCYCLE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #MCYCLE Write clear/set value 0x1f
    csrrci x14, 0xb00, 0x0
    csrrsi x14, 0xb00, 0x1f

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x0
    csrrci x14, 0xb00, 0x1f
    csrrsi x14, 0xb00, 0x0

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x15
    csrrci x14, 0xb00, 0xa
    csrrsi x14, 0xb00, 0x15

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0xa
    csrrci x14, 0xb00, 0x15
    csrrsi x14, 0xb00, 0xa

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x18
    csrrci x14, 0xb00, 0x7
    csrrsi x14, 0xb00, 0x18

    #MCYCLE read value
    csrr x14, 0xb00

    ##########################
    #MHPMCOUNTER8 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h12} 
    ##########################
    #MHPMCOUNTER8 Write clear/set value 0x1f
    csrrci x14, 0xb08, 0x0
    csrrsi x14, 0xb08, 0x1f

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write clear/set value 0x0
    csrrci x14, 0xb08, 0x1f
    csrrsi x14, 0xb08, 0x0

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write clear/set value 0x15
    csrrci x14, 0xb08, 0xa
    csrrsi x14, 0xb08, 0x15

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write clear/set value 0xa
    csrrci x14, 0xb08, 0x15
    csrrsi x14, 0xb08, 0xa

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write clear/set value 0x12
    csrrci x14, 0xb08, 0xd
    csrrsi x14, 0xb08, 0x12

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    ##########################
    #MHPMEVENT18 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hc} 
    ##########################
    #MHPMEVENT18 Write clear/set value 0x1f
    csrrci x14, 0x332, 0x0
    csrrsi x14, 0x332, 0x1f

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write clear/set value 0x0
    csrrci x14, 0x332, 0x1f
    csrrsi x14, 0x332, 0x0

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write clear/set value 0x15
    csrrci x14, 0x332, 0xa
    csrrsi x14, 0x332, 0x15

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write clear/set value 0xa
    csrrci x14, 0x332, 0x15
    csrrsi x14, 0x332, 0xa

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write clear/set value 0xc
    csrrci x14, 0x332, 0x13
    csrrsi x14, 0x332, 0xc

    #MHPMEVENT18 read value
    csrr x14, 0x332

    ##########################
    #PMPADDR5 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h13} 
    ##########################
    #PMPADDR5 Write clear/set value 0x1f
    csrrci x14, 0x3b5, 0x0
    csrrsi x14, 0x3b5, 0x1f

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write clear/set value 0x0
    csrrci x14, 0x3b5, 0x1f
    csrrsi x14, 0x3b5, 0x0

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write clear/set value 0x15
    csrrci x14, 0x3b5, 0xa
    csrrsi x14, 0x3b5, 0x15

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write clear/set value 0xa
    csrrci x14, 0x3b5, 0x15
    csrrsi x14, 0x3b5, 0xa

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write clear/set value 0x13
    csrrci x14, 0x3b5, 0xc
    csrrsi x14, 0x3b5, 0x13

    #PMPADDR5 read value
    csrr x14, 0x3b5

    ##########################
    #MHPMEVENT12 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #MHPMEVENT12 Write clear/set value 0x1f
    csrrci x14, 0x32c, 0x0
    csrrsi x14, 0x32c, 0x1f

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write clear/set value 0x0
    csrrci x14, 0x32c, 0x1f
    csrrsi x14, 0x32c, 0x0

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write clear/set value 0x15
    csrrci x14, 0x32c, 0xa
    csrrsi x14, 0x32c, 0x15

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write clear/set value 0xa
    csrrci x14, 0x32c, 0x15
    csrrsi x14, 0x32c, 0xa

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write clear/set value 0x1
    csrrci x14, 0x32c, 0x1e
    csrrsi x14, 0x32c, 0x1

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    ##########################
    #MHPMEVENT30 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h17} 
    ##########################
    #MHPMEVENT30 Write clear/set value 0x1f
    csrrci x14, 0x33e, 0x0
    csrrsi x14, 0x33e, 0x1f

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write clear/set value 0x0
    csrrci x14, 0x33e, 0x1f
    csrrsi x14, 0x33e, 0x0

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write clear/set value 0x15
    csrrci x14, 0x33e, 0xa
    csrrsi x14, 0x33e, 0x15

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write clear/set value 0xa
    csrrci x14, 0x33e, 0x15
    csrrsi x14, 0x33e, 0xa

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write clear/set value 0x17
    csrrci x14, 0x33e, 0x8
    csrrsi x14, 0x33e, 0x17

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    ##########################
    #MHPMEVENT4 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16} 
    ##########################
    #MHPMEVENT4 Write clear/set value 0x1f
    csrrci x14, 0x324, 0x0
    csrrsi x14, 0x324, 0x1f

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write clear/set value 0x0
    csrrci x14, 0x324, 0x1f
    csrrsi x14, 0x324, 0x0

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write clear/set value 0x15
    csrrci x14, 0x324, 0xa
    csrrsi x14, 0x324, 0x15

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write clear/set value 0xa
    csrrci x14, 0x324, 0x15
    csrrsi x14, 0x324, 0xa

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write clear/set value 0x16
    csrrci x14, 0x324, 0x9
    csrrsi x14, 0x324, 0x16

    #MHPMEVENT4 read value
    csrr x14, 0x324

    ##########################
    #MHPMCOUNTERH17 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1e} 
    ##########################
    #MHPMCOUNTERH17 Write clear/set value 0x1f
    csrrci x14, 0xb91, 0x0
    csrrsi x14, 0xb91, 0x1f

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write clear/set value 0x0
    csrrci x14, 0xb91, 0x1f
    csrrsi x14, 0xb91, 0x0

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write clear/set value 0x15
    csrrci x14, 0xb91, 0xa
    csrrsi x14, 0xb91, 0x15

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write clear/set value 0xa
    csrrci x14, 0xb91, 0x15
    csrrsi x14, 0xb91, 0xa

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write clear/set value 0x1e
    csrrci x14, 0xb91, 0x1
    csrrsi x14, 0xb91, 0x1e

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    ##########################
    #MIP testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a} 
    ##########################
    #MIP Write clear/set value 0x1f
    csrrci x14, 0x344, 0x0
    csrrsi x14, 0x344, 0x1f

    #MIP read value
    csrr x14, 0x344

    #MIP Write clear/set value 0x0
    csrrci x14, 0x344, 0x17
    csrrsi x14, 0x344, 0x0

    #MIP read value
    csrr x14, 0x344

    #MIP Write clear/set value 0x15
    csrrci x14, 0x344, 0x2
    csrrsi x14, 0x344, 0x15

    #MIP read value
    csrr x14, 0x344

    #MIP Write clear/set value 0xa
    csrrci x14, 0x344, 0x15
    csrrsi x14, 0x344, 0xa

    #MIP read value
    csrr x14, 0x344

    #MIP Write clear/set value 0x1a
    csrrci x14, 0x344, 0x5
    csrrsi x14, 0x344, 0x1a

    #MIP read value
    csrr x14, 0x344

    #Clear MIP to avoid traping
    csrw 0x344, x0

    #MIP read value
    csrr x14, 0x344

    ##########################
    #MHPMCOUNTERH11 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h11} 
    ##########################
    #MHPMCOUNTERH11 Write clear/set value 0x1f
    csrrci x14, 0xb8b, 0x0
    csrrsi x14, 0xb8b, 0x1f

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write clear/set value 0x0
    csrrci x14, 0xb8b, 0x1f
    csrrsi x14, 0xb8b, 0x0

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write clear/set value 0x15
    csrrci x14, 0xb8b, 0xa
    csrrsi x14, 0xb8b, 0x15

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write clear/set value 0xa
    csrrci x14, 0xb8b, 0x15
    csrrsi x14, 0xb8b, 0xa

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write clear/set value 0x11
    csrrci x14, 0xb8b, 0xe
    csrrsi x14, 0xb8b, 0x11

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    ##########################
    #MHPMCOUNTER9 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h0} 
    ##########################
    #MHPMCOUNTER9 Write clear/set value 0x1f
    csrrci x14, 0xb09, 0x0
    csrrsi x14, 0xb09, 0x1f

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write clear/set value 0x0
    csrrci x14, 0xb09, 0x1f
    csrrsi x14, 0xb09, 0x0

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write clear/set value 0x15
    csrrci x14, 0xb09, 0xa
    csrrsi x14, 0xb09, 0x15

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write clear/set value 0xa
    csrrci x14, 0xb09, 0x15
    csrrsi x14, 0xb09, 0xa

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write clear/set value 0x0
    csrrci x14, 0xb09, 0x1f
    csrrsi x14, 0xb09, 0x0

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    ##########################
    #MSCRATCH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #MSCRATCH Write clear/set value 0x1f
    csrrci x14, 0x340, 0x0
    csrrsi x14, 0x340, 0x1f

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x0
    csrrci x14, 0x340, 0x1f
    csrrsi x14, 0x340, 0x0

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x15
    csrrci x14, 0x340, 0xa
    csrrsi x14, 0x340, 0x15

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0xa
    csrrci x14, 0x340, 0x15
    csrrsi x14, 0x340, 0xa

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x10
    csrrci x14, 0x340, 0xf
    csrrsi x14, 0x340, 0x10

    #MSCRATCH read value
    csrr x14, 0x340

    ##########################
    #MHPMCOUNTERH16 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h15} 
    ##########################
    #MHPMCOUNTERH16 Write clear/set value 0x1f
    csrrci x14, 0xb90, 0x0
    csrrsi x14, 0xb90, 0x1f

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write clear/set value 0x0
    csrrci x14, 0xb90, 0x1f
    csrrsi x14, 0xb90, 0x0

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write clear/set value 0x15
    csrrci x14, 0xb90, 0xa
    csrrsi x14, 0xb90, 0x15

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write clear/set value 0xa
    csrrci x14, 0xb90, 0x15
    csrrsi x14, 0xb90, 0xa

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write clear/set value 0x15
    csrrci x14, 0xb90, 0xa
    csrrsi x14, 0xb90, 0x15

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    ##########################
    #MHPMCOUNTERH12 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4} 
    ##########################
    #MHPMCOUNTERH12 Write clear/set value 0x1f
    csrrci x14, 0xb8c, 0x0
    csrrsi x14, 0xb8c, 0x1f

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write clear/set value 0x0
    csrrci x14, 0xb8c, 0x1f
    csrrsi x14, 0xb8c, 0x0

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write clear/set value 0x15
    csrrci x14, 0xb8c, 0xa
    csrrsi x14, 0xb8c, 0x15

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write clear/set value 0xa
    csrrci x14, 0xb8c, 0x15
    csrrsi x14, 0xb8c, 0xa

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write clear/set value 0x4
    csrrci x14, 0xb8c, 0x1b
    csrrsi x14, 0xb8c, 0x4

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    ##########################
    #PMPADDR4 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1e} 
    ##########################
    #PMPADDR4 Write clear/set value 0x1f
    csrrci x14, 0x3b4, 0x0
    csrrsi x14, 0x3b4, 0x1f

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write clear/set value 0x0
    csrrci x14, 0x3b4, 0x1f
    csrrsi x14, 0x3b4, 0x0

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write clear/set value 0x15
    csrrci x14, 0x3b4, 0xa
    csrrsi x14, 0x3b4, 0x15

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write clear/set value 0xa
    csrrci x14, 0x3b4, 0x15
    csrrsi x14, 0x3b4, 0xa

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write clear/set value 0x1e
    csrrci x14, 0x3b4, 0x1
    csrrsi x14, 0x3b4, 0x1e

    #PMPADDR4 read value
    csrr x14, 0x3b4

    ##########################
    #MHPMEVENT24 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hc} 
    ##########################
    #MHPMEVENT24 Write clear/set value 0x1f
    csrrci x14, 0x338, 0x0
    csrrsi x14, 0x338, 0x1f

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write clear/set value 0x0
    csrrci x14, 0x338, 0x1f
    csrrsi x14, 0x338, 0x0

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write clear/set value 0x15
    csrrci x14, 0x338, 0xa
    csrrsi x14, 0x338, 0x15

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write clear/set value 0xa
    csrrci x14, 0x338, 0x15
    csrrsi x14, 0x338, 0xa

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write clear/set value 0xc
    csrrci x14, 0x338, 0x13
    csrrsi x14, 0x338, 0xc

    #MHPMEVENT24 read value
    csrr x14, 0x338

    ##########################
    #PMPADDR8 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #PMPADDR8 Write clear/set value 0x1f
    csrrci x14, 0x3b8, 0x0
    csrrsi x14, 0x3b8, 0x1f

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write clear/set value 0x0
    csrrci x14, 0x3b8, 0x1f
    csrrsi x14, 0x3b8, 0x0

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write clear/set value 0x15
    csrrci x14, 0x3b8, 0xa
    csrrsi x14, 0x3b8, 0x15

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write clear/set value 0xa
    csrrci x14, 0x3b8, 0x15
    csrrsi x14, 0x3b8, 0xa

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write clear/set value 0x18
    csrrci x14, 0x3b8, 0x7
    csrrsi x14, 0x3b8, 0x18

    #PMPADDR8 read value
    csrr x14, 0x3b8

    ##########################
    #MCAUSE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h0} 
    ##########################
    #MCAUSE Write clear/set value 0x1f
    csrrci x14, 0x342, 0x0
    csrrsi x14, 0x342, 0x1f

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x0
    csrrci x14, 0x342, 0x1f
    csrrsi x14, 0x342, 0x0

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x15
    csrrci x14, 0x342, 0xa
    csrrsi x14, 0x342, 0x15

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0xa
    csrrci x14, 0x342, 0x15
    csrrsi x14, 0x342, 0xa

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x0
    csrrci x14, 0x342, 0x1f
    csrrsi x14, 0x342, 0x0

    #MCAUSE read value
    csrr x14, 0x342

    ##########################
    #MHPMEVENT23 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1e} 
    ##########################
    #MHPMEVENT23 Write clear/set value 0x1f
    csrrci x14, 0x337, 0x0
    csrrsi x14, 0x337, 0x1f

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write clear/set value 0x0
    csrrci x14, 0x337, 0x1f
    csrrsi x14, 0x337, 0x0

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write clear/set value 0x15
    csrrci x14, 0x337, 0xa
    csrrsi x14, 0x337, 0x15

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write clear/set value 0xa
    csrrci x14, 0x337, 0x15
    csrrsi x14, 0x337, 0xa

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write clear/set value 0x1e
    csrrci x14, 0x337, 0x1
    csrrsi x14, 0x337, 0x1e

    #MHPMEVENT23 read value
    csrr x14, 0x337

    ##########################
    #PMPADDR2 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #PMPADDR2 Write clear/set value 0x1f
    csrrci x14, 0x3b2, 0x0
    csrrsi x14, 0x3b2, 0x1f

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write clear/set value 0x0
    csrrci x14, 0x3b2, 0x1f
    csrrsi x14, 0x3b2, 0x0

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write clear/set value 0x15
    csrrci x14, 0x3b2, 0xa
    csrrsi x14, 0x3b2, 0x15

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write clear/set value 0xa
    csrrci x14, 0x3b2, 0x15
    csrrsi x14, 0x3b2, 0xa

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write clear/set value 0x19
    csrrci x14, 0x3b2, 0x6
    csrrsi x14, 0x3b2, 0x19

    #PMPADDR2 read value
    csrr x14, 0x3b2

    ##########################
    #PMPADDR6 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4} 
    ##########################
    #PMPADDR6 Write clear/set value 0x1f
    csrrci x14, 0x3b6, 0x0
    csrrsi x14, 0x3b6, 0x1f

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write clear/set value 0x0
    csrrci x14, 0x3b6, 0x1f
    csrrsi x14, 0x3b6, 0x0

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write clear/set value 0x15
    csrrci x14, 0x3b6, 0xa
    csrrsi x14, 0x3b6, 0x15

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write clear/set value 0xa
    csrrci x14, 0x3b6, 0x15
    csrrsi x14, 0x3b6, 0xa

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write clear/set value 0x4
    csrrci x14, 0x3b6, 0x1b
    csrrsi x14, 0x3b6, 0x4

    #PMPADDR6 read value
    csrr x14, 0x3b6

    ##########################
    #PMPCFG0 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h9} 
    ##########################
    #PMPCFG0 Write clear/set value 0x1f
    csrrci x14, 0x3a0, 0x0
    csrrsi x14, 0x3a0, 0x1f

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write clear/set value 0x0
    csrrci x14, 0x3a0, 0x1f
    csrrsi x14, 0x3a0, 0x0

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write clear/set value 0x15
    csrrci x14, 0x3a0, 0xa
    csrrsi x14, 0x3a0, 0x15

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write clear/set value 0xa
    csrrci x14, 0x3a0, 0x15
    csrrsi x14, 0x3a0, 0xa

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write clear/set value 0x9
    csrrci x14, 0x3a0, 0x16
    csrrsi x14, 0x3a0, 0x9

    #PMPCFG0 read value
    csrr x14, 0x3a0

    ##########################
    #MHPMCOUNTER28 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h12} 
    ##########################
    #MHPMCOUNTER28 Write clear/set value 0x1f
    csrrci x14, 0xb1c, 0x0
    csrrsi x14, 0xb1c, 0x1f

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write clear/set value 0x0
    csrrci x14, 0xb1c, 0x1f
    csrrsi x14, 0xb1c, 0x0

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write clear/set value 0x15
    csrrci x14, 0xb1c, 0xa
    csrrsi x14, 0xb1c, 0x15

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write clear/set value 0xa
    csrrci x14, 0xb1c, 0x15
    csrrsi x14, 0xb1c, 0xa

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write clear/set value 0x12
    csrrci x14, 0xb1c, 0xd
    csrrsi x14, 0xb1c, 0x12

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    ##########################
    #MHPMEVENT26 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h0} 
    ##########################
    #MHPMEVENT26 Write clear/set value 0x1f
    csrrci x14, 0x33a, 0x0
    csrrsi x14, 0x33a, 0x1f

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write clear/set value 0x0
    csrrci x14, 0x33a, 0x1f
    csrrsi x14, 0x33a, 0x0

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write clear/set value 0x15
    csrrci x14, 0x33a, 0xa
    csrrsi x14, 0x33a, 0x15

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write clear/set value 0xa
    csrrci x14, 0x33a, 0x15
    csrrsi x14, 0x33a, 0xa

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write clear/set value 0x0
    csrrci x14, 0x33a, 0x1f
    csrrsi x14, 0x33a, 0x0

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    ##########################
    #MHPMCOUNTERH28 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h5} 
    ##########################
    #MHPMCOUNTERH28 Write clear/set value 0x1f
    csrrci x14, 0xb9c, 0x0
    csrrsi x14, 0xb9c, 0x1f

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write clear/set value 0x0
    csrrci x14, 0xb9c, 0x1f
    csrrsi x14, 0xb9c, 0x0

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write clear/set value 0x15
    csrrci x14, 0xb9c, 0xa
    csrrsi x14, 0xb9c, 0x15

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write clear/set value 0xa
    csrrci x14, 0xb9c, 0x15
    csrrsi x14, 0xb9c, 0xa

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write clear/set value 0x5
    csrrci x14, 0xb9c, 0x1a
    csrrsi x14, 0xb9c, 0x5

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    ##########################
    #MHPMCOUNTERH30 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h13} 
    ##########################
    #MHPMCOUNTERH30 Write clear/set value 0x1f
    csrrci x14, 0xb9e, 0x0
    csrrsi x14, 0xb9e, 0x1f

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write clear/set value 0x0
    csrrci x14, 0xb9e, 0x1f
    csrrsi x14, 0xb9e, 0x0

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write clear/set value 0x15
    csrrci x14, 0xb9e, 0xa
    csrrsi x14, 0xb9e, 0x15

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write clear/set value 0xa
    csrrci x14, 0xb9e, 0x15
    csrrsi x14, 0xb9e, 0xa

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write clear/set value 0x13
    csrrci x14, 0xb9e, 0xc
    csrrsi x14, 0xb9e, 0x13

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    ##########################
    #MHPMCOUNTER16 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h12} 
    ##########################
    #MHPMCOUNTER16 Write clear/set value 0x1f
    csrrci x14, 0xb10, 0x0
    csrrsi x14, 0xb10, 0x1f

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write clear/set value 0x0
    csrrci x14, 0xb10, 0x1f
    csrrsi x14, 0xb10, 0x0

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write clear/set value 0x15
    csrrci x14, 0xb10, 0xa
    csrrsi x14, 0xb10, 0x15

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write clear/set value 0xa
    csrrci x14, 0xb10, 0x15
    csrrsi x14, 0xb10, 0xa

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write clear/set value 0x12
    csrrci x14, 0xb10, 0xd
    csrrsi x14, 0xb10, 0x12

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    ##########################
    #PMPADDR13 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #PMPADDR13 Write clear/set value 0x1f
    csrrci x14, 0x3bd, 0x0
    csrrsi x14, 0x3bd, 0x1f

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write clear/set value 0x0
    csrrci x14, 0x3bd, 0x1f
    csrrsi x14, 0x3bd, 0x0

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write clear/set value 0x15
    csrrci x14, 0x3bd, 0xa
    csrrsi x14, 0x3bd, 0x15

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write clear/set value 0xa
    csrrci x14, 0x3bd, 0x15
    csrrsi x14, 0x3bd, 0xa

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write clear/set value 0x1
    csrrci x14, 0x3bd, 0x1e
    csrrsi x14, 0x3bd, 0x1

    #PMPADDR13 read value
    csrr x14, 0x3bd

    ##########################
    #MHPMCOUNTERH27 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a} 
    ##########################
    #MHPMCOUNTERH27 Write clear/set value 0x1f
    csrrci x14, 0xb9b, 0x0
    csrrsi x14, 0xb9b, 0x1f

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write clear/set value 0x0
    csrrci x14, 0xb9b, 0x1f
    csrrsi x14, 0xb9b, 0x0

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write clear/set value 0x15
    csrrci x14, 0xb9b, 0xa
    csrrsi x14, 0xb9b, 0x15

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write clear/set value 0xa
    csrrci x14, 0xb9b, 0x15
    csrrsi x14, 0xb9b, 0xa

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write clear/set value 0x1a
    csrrci x14, 0xb9b, 0x5
    csrrsi x14, 0xb9b, 0x1a

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    ##########################
    #MHPMEVENT27 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h11} 
    ##########################
    #MHPMEVENT27 Write clear/set value 0x1f
    csrrci x14, 0x33b, 0x0
    csrrsi x14, 0x33b, 0x1f

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write clear/set value 0x0
    csrrci x14, 0x33b, 0x1f
    csrrsi x14, 0x33b, 0x0

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write clear/set value 0x15
    csrrci x14, 0x33b, 0xa
    csrrsi x14, 0x33b, 0x15

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write clear/set value 0xa
    csrrci x14, 0x33b, 0x15
    csrrsi x14, 0x33b, 0xa

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write clear/set value 0x11
    csrrci x14, 0x33b, 0xe
    csrrsi x14, 0x33b, 0x11

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    ##########################
    #MHPMCOUNTERH7 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'ha} 
    ##########################
    #MHPMCOUNTERH7 Write clear/set value 0x1f
    csrrci x14, 0xb87, 0x0
    csrrsi x14, 0xb87, 0x1f

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write clear/set value 0x0
    csrrci x14, 0xb87, 0x1f
    csrrsi x14, 0xb87, 0x0

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write clear/set value 0x15
    csrrci x14, 0xb87, 0xa
    csrrsi x14, 0xb87, 0x15

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write clear/set value 0xa
    csrrci x14, 0xb87, 0x15
    csrrsi x14, 0xb87, 0xa

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write clear/set value 0xa
    csrrci x14, 0xb87, 0x15
    csrrsi x14, 0xb87, 0xa

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    ##########################
    #MHPMCOUNTER12 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h12} 
    ##########################
    #MHPMCOUNTER12 Write clear/set value 0x1f
    csrrci x14, 0xb0c, 0x0
    csrrsi x14, 0xb0c, 0x1f

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write clear/set value 0x0
    csrrci x14, 0xb0c, 0x1f
    csrrsi x14, 0xb0c, 0x0

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write clear/set value 0x15
    csrrci x14, 0xb0c, 0xa
    csrrsi x14, 0xb0c, 0x15

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write clear/set value 0xa
    csrrci x14, 0xb0c, 0x15
    csrrsi x14, 0xb0c, 0xa

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write clear/set value 0x12
    csrrci x14, 0xb0c, 0xd
    csrrsi x14, 0xb0c, 0x12

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    ##########################
    #MHPMEVENT16 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1b} 
    ##########################
    #MHPMEVENT16 Write clear/set value 0x1f
    csrrci x14, 0x330, 0x0
    csrrsi x14, 0x330, 0x1f

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write clear/set value 0x0
    csrrci x14, 0x330, 0x1f
    csrrsi x14, 0x330, 0x0

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write clear/set value 0x15
    csrrci x14, 0x330, 0xa
    csrrsi x14, 0x330, 0x15

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write clear/set value 0xa
    csrrci x14, 0x330, 0x15
    csrrsi x14, 0x330, 0xa

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write clear/set value 0x1b
    csrrci x14, 0x330, 0x4
    csrrsi x14, 0x330, 0x1b

    #MHPMEVENT16 read value
    csrr x14, 0x330

    ##########################
    #MHPMCOUNTERH19 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16} 
    ##########################
    #MHPMCOUNTERH19 Write clear/set value 0x1f
    csrrci x14, 0xb93, 0x0
    csrrsi x14, 0xb93, 0x1f

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write clear/set value 0x0
    csrrci x14, 0xb93, 0x1f
    csrrsi x14, 0xb93, 0x0

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write clear/set value 0x15
    csrrci x14, 0xb93, 0xa
    csrrsi x14, 0xb93, 0x15

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write clear/set value 0xa
    csrrci x14, 0xb93, 0x15
    csrrsi x14, 0xb93, 0xa

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write clear/set value 0x16
    csrrci x14, 0xb93, 0x9
    csrrsi x14, 0xb93, 0x16

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    ##########################
    #MHPMCOUNTER22 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #MHPMCOUNTER22 Write clear/set value 0x1f
    csrrci x14, 0xb16, 0x0
    csrrsi x14, 0xb16, 0x1f

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write clear/set value 0x0
    csrrci x14, 0xb16, 0x1f
    csrrsi x14, 0xb16, 0x0

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write clear/set value 0x15
    csrrci x14, 0xb16, 0xa
    csrrsi x14, 0xb16, 0x15

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write clear/set value 0xa
    csrrci x14, 0xb16, 0x15
    csrrsi x14, 0xb16, 0xa

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write clear/set value 0x19
    csrrci x14, 0xb16, 0x6
    csrrsi x14, 0xb16, 0x19

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    ##########################
    #MHPMEVENT15 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hf} 
    ##########################
    #MHPMEVENT15 Write clear/set value 0x1f
    csrrci x14, 0x32f, 0x0
    csrrsi x14, 0x32f, 0x1f

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write clear/set value 0x0
    csrrci x14, 0x32f, 0x1f
    csrrsi x14, 0x32f, 0x0

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write clear/set value 0x15
    csrrci x14, 0x32f, 0xa
    csrrsi x14, 0x32f, 0x15

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write clear/set value 0xa
    csrrci x14, 0x32f, 0x15
    csrrsi x14, 0x32f, 0xa

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write clear/set value 0xf
    csrrci x14, 0x32f, 0x10
    csrrsi x14, 0x32f, 0xf

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    ##########################
    #PMPADDR7 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #PMPADDR7 Write clear/set value 0x1f
    csrrci x14, 0x3b7, 0x0
    csrrsi x14, 0x3b7, 0x1f

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write clear/set value 0x0
    csrrci x14, 0x3b7, 0x1f
    csrrsi x14, 0x3b7, 0x0

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write clear/set value 0x15
    csrrci x14, 0x3b7, 0xa
    csrrsi x14, 0x3b7, 0x15

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write clear/set value 0xa
    csrrci x14, 0x3b7, 0x15
    csrrsi x14, 0x3b7, 0xa

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write clear/set value 0x18
    csrrci x14, 0x3b7, 0x7
    csrrsi x14, 0x3b7, 0x18

    #PMPADDR7 read value
    csrr x14, 0x3b7

    ##########################
    #MHPMEVENT9 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h6} 
    ##########################
    #MHPMEVENT9 Write clear/set value 0x1f
    csrrci x14, 0x329, 0x0
    csrrsi x14, 0x329, 0x1f

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write clear/set value 0x0
    csrrci x14, 0x329, 0x1f
    csrrsi x14, 0x329, 0x0

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write clear/set value 0x15
    csrrci x14, 0x329, 0xa
    csrrsi x14, 0x329, 0x15

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write clear/set value 0xa
    csrrci x14, 0x329, 0x15
    csrrsi x14, 0x329, 0xa

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write clear/set value 0x6
    csrrci x14, 0x329, 0x19
    csrrsi x14, 0x329, 0x6

    #MHPMEVENT9 read value
    csrr x14, 0x329

    ret
