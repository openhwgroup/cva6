# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

csrcs:
    #Start CSR tests: Write/Read all RW registers registers in a random order using Clear/Set instructions
    #User ignored registers: 

    ##########################
    #MTVAL testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16}
    ##########################
    #MTVAL Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x343, x3
    li x3, 0x1f
    csrrs x14, 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x343, x3
    li x3, 0x0
    csrrs x14, 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x343, x3
    li x3, 0x15
    csrrs x14, 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x343, x3
    li x3, 0xa
    csrrs x14, 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    #MTVAL Write clear/set value 0x16
    li x3, 0xffffffe9
    csrrc x14, 0x343, x3
    li x3, 0x16
    csrrs x14, 0x343, x3

    #MTVAL read value
    csrr x14, 0x343

    ##########################
    #MHPMEVENT22 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16} 
    ##########################
    #MHPMEVENT22 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x336, x3
    li x3, 0x1f
    csrrs x14, 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x336, x3
    li x3, 0x0
    csrrs x14, 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x336, x3
    li x3, 0x15
    csrrs x14, 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x336, x3
    li x3, 0xa
    csrrs x14, 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    #MHPMEVENT22 Write clear/set value 0x16
    li x3, 0xffffffe9
    csrrc x14, 0x336, x3
    li x3, 0x16
    csrrs x14, 0x336, x3

    #MHPMEVENT22 read value
    csrr x14, 0x336

    ##########################
    #MHPMCOUNTERH16 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #MHPMCOUNTERH16 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb90, x3
    li x3, 0x1f
    csrrs x14, 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb90, x3
    li x3, 0x0
    csrrs x14, 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb90, x3
    li x3, 0x15
    csrrs x14, 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb90, x3
    li x3, 0xa
    csrrs x14, 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    #MHPMCOUNTERH16 Write clear/set value 0x10
    li x3, 0xffffffef
    csrrc x14, 0xb90, x3
    li x3, 0x10
    csrrs x14, 0xb90, x3

    #MHPMCOUNTERH16 read value
    csrr x14, 0xb90

    ##########################
    #MHPMCOUNTERH12 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #MHPMCOUNTERH12 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb8c, x3
    li x3, 0x1f
    csrrs x14, 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb8c, x3
    li x3, 0x0
    csrrs x14, 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb8c, x3
    li x3, 0x15
    csrrs x14, 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb8c, x3
    li x3, 0xa
    csrrs x14, 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    #MHPMCOUNTERH12 Write clear/set value 0x18
    li x3, 0xffffffe7
    csrrc x14, 0xb8c, x3
    li x3, 0x18
    csrrs x14, 0xb8c, x3

    #MHPMCOUNTERH12 read value
    csrr x14, 0xb8c

    ##########################
    #MHPMEVENT25 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h9} 
    ##########################
    #MHPMEVENT25 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x339, x3
    li x3, 0x1f
    csrrs x14, 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x339, x3
    li x3, 0x0
    csrrs x14, 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x339, x3
    li x3, 0x15
    csrrs x14, 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x339, x3
    li x3, 0xa
    csrrs x14, 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    #MHPMEVENT25 Write clear/set value 0x9
    li x3, 0xfffffff6
    csrrc x14, 0x339, x3
    li x3, 0x9
    csrrs x14, 0x339, x3

    #MHPMEVENT25 read value
    csrr x14, 0x339

    ##########################
    #MHPMCOUNTERH10 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMCOUNTERH10 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb8a, x3
    li x3, 0x1f
    csrrs x14, 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb8a, x3
    li x3, 0x0
    csrrs x14, 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb8a, x3
    li x3, 0x15
    csrrs x14, 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb8a, x3
    li x3, 0xa
    csrrs x14, 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    #MHPMCOUNTERH10 Write clear/set value 0x2
    li x3, 0xfffffffd
    csrrc x14, 0xb8a, x3
    li x3, 0x2
    csrrs x14, 0xb8a, x3

    #MHPMCOUNTERH10 read value
    csrr x14, 0xb8a

    ##########################
    #PMPADDR1 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h14} 
    ##########################
    #PMPADDR1 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b1, x3
    li x3, 0x1f
    csrrs x14, 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b1, x3
    li x3, 0x0
    csrrs x14, 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b1, x3
    li x3, 0x15
    csrrs x14, 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b1, x3
    li x3, 0xa
    csrrs x14, 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    #PMPADDR1 Write clear/set value 0x14
    li x3, 0xffffffeb
    csrrc x14, 0x3b1, x3
    li x3, 0x14
    csrrs x14, 0x3b1, x3

    #PMPADDR1 read value
    csrr x14, 0x3b1

    ##########################
    #MHPMCOUNTER23 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'he} 
    ##########################
    #MHPMCOUNTER23 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb17, x3
    li x3, 0x1f
    csrrs x14, 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb17, x3
    li x3, 0x0
    csrrs x14, 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb17, x3
    li x3, 0x15
    csrrs x14, 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb17, x3
    li x3, 0xa
    csrrs x14, 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    #MHPMCOUNTER23 Write clear/set value 0xe
    li x3, 0xfffffff1
    csrrc x14, 0xb17, x3
    li x3, 0xe
    csrrs x14, 0xb17, x3

    #MHPMCOUNTER23 read value
    csrr x14, 0xb17

    ##########################
    #MHPMEVENT8 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7} 
    ##########################
    #MHPMEVENT8 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x328, x3
    li x3, 0x1f
    csrrs x14, 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x328, x3
    li x3, 0x0
    csrrs x14, 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x328, x3
    li x3, 0x15
    csrrs x14, 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x328, x3
    li x3, 0xa
    csrrs x14, 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    #MHPMEVENT8 Write clear/set value 0x7
    li x3, 0xfffffff8
    csrrc x14, 0x328, x3
    li x3, 0x7
    csrrs x14, 0x328, x3

    #MHPMEVENT8 read value
    csrr x14, 0x328

    ##########################
    #MHPMCOUNTERH5 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4} 
    ##########################
    #MHPMCOUNTERH5 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb85, x3
    li x3, 0x1f
    csrrs x14, 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb85, x3
    li x3, 0x0
    csrrs x14, 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb85, x3
    li x3, 0x15
    csrrs x14, 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb85, x3
    li x3, 0xa
    csrrs x14, 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    #MHPMCOUNTERH5 Write clear/set value 0x4
    li x3, 0xfffffffb
    csrrc x14, 0xb85, x3
    li x3, 0x4
    csrrs x14, 0xb85, x3

    #MHPMCOUNTERH5 read value
    csrr x14, 0xb85

    ##########################
    #MHPMEVENT23 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16} 
    ##########################
    #MHPMEVENT23 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x337, x3
    li x3, 0x1f
    csrrs x14, 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x337, x3
    li x3, 0x0
    csrrs x14, 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x337, x3
    li x3, 0x15
    csrrs x14, 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x337, x3
    li x3, 0xa
    csrrs x14, 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    #MHPMEVENT23 Write clear/set value 0x16
    li x3, 0xffffffe9
    csrrc x14, 0x337, x3
    li x3, 0x16
    csrrs x14, 0x337, x3

    #MHPMEVENT23 read value
    csrr x14, 0x337

    ##########################
    #MHPMCOUNTER10 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f} 
    ##########################
    #MHPMCOUNTER10 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb0a, x3
    li x3, 0x1f
    csrrs x14, 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb0a, x3
    li x3, 0x0
    csrrs x14, 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb0a, x3
    li x3, 0x15
    csrrs x14, 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb0a, x3
    li x3, 0xa
    csrrs x14, 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    #MHPMCOUNTER10 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb0a, x3
    li x3, 0x1f
    csrrs x14, 0xb0a, x3

    #MHPMCOUNTER10 read value
    csrr x14, 0xb0a

    ##########################
    #MHPMCOUNTERH27 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #MHPMCOUNTERH27 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb9b, x3
    li x3, 0x1f
    csrrs x14, 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb9b, x3
    li x3, 0x0
    csrrs x14, 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb9b, x3
    li x3, 0x15
    csrrs x14, 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb9b, x3
    li x3, 0xa
    csrrs x14, 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    #MHPMCOUNTERH27 Write clear/set value 0x10
    li x3, 0xffffffef
    csrrc x14, 0xb9b, x3
    li x3, 0x10
    csrrs x14, 0xb9b, x3

    #MHPMCOUNTERH27 read value
    csrr x14, 0xb9b

    ##########################
    #MHPMCOUNTER18 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h3} 
    ##########################
    #MHPMCOUNTER18 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb12, x3
    li x3, 0x1f
    csrrs x14, 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb12, x3
    li x3, 0x0
    csrrs x14, 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb12, x3
    li x3, 0x15
    csrrs x14, 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb12, x3
    li x3, 0xa
    csrrs x14, 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    #MHPMCOUNTER18 Write clear/set value 0x3
    li x3, 0xfffffffc
    csrrc x14, 0xb12, x3
    li x3, 0x3
    csrrs x14, 0xb12, x3

    #MHPMCOUNTER18 read value
    csrr x14, 0xb12

    ##########################
    #MHPMEVENT18 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMEVENT18 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x332, x3
    li x3, 0x1f
    csrrs x14, 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x332, x3
    li x3, 0x0
    csrrs x14, 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x332, x3
    li x3, 0x15
    csrrs x14, 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x332, x3
    li x3, 0xa
    csrrs x14, 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    #MHPMEVENT18 Write clear/set value 0x2
    li x3, 0xfffffffd
    csrrc x14, 0x332, x3
    li x3, 0x2
    csrrs x14, 0x332, x3

    #MHPMEVENT18 read value
    csrr x14, 0x332

    ##########################
    #MHPMEVENT16 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #MHPMEVENT16 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x330, x3
    li x3, 0x1f
    csrrs x14, 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x330, x3
    li x3, 0x0
    csrrs x14, 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x330, x3
    li x3, 0x15
    csrrs x14, 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x330, x3
    li x3, 0xa
    csrrs x14, 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    #MHPMEVENT16 Write clear/set value 0xd
    li x3, 0xfffffff2
    csrrc x14, 0x330, x3
    li x3, 0xd
    csrrs x14, 0x330, x3

    #MHPMEVENT16 read value
    csrr x14, 0x330

    ##########################
    #MHPMEVENT14 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h6} 
    ##########################
    #MHPMEVENT14 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x32e, x3
    li x3, 0x1f
    csrrs x14, 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x32e, x3
    li x3, 0x0
    csrrs x14, 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x32e, x3
    li x3, 0x15
    csrrs x14, 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x32e, x3
    li x3, 0xa
    csrrs x14, 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    #MHPMEVENT14 Write clear/set value 0x6
    li x3, 0xfffffff9
    csrrc x14, 0x32e, x3
    li x3, 0x6
    csrrs x14, 0x32e, x3

    #MHPMEVENT14 read value
    csrr x14, 0x32e

    ##########################
    #MHPMCOUNTER21 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMCOUNTER21 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb15, x3
    li x3, 0x1f
    csrrs x14, 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb15, x3
    li x3, 0x0
    csrrs x14, 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb15, x3
    li x3, 0x15
    csrrs x14, 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb15, x3
    li x3, 0xa
    csrrs x14, 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    #MHPMCOUNTER21 Write clear/set value 0x2
    li x3, 0xfffffffd
    csrrc x14, 0xb15, x3
    li x3, 0x2
    csrrs x14, 0xb15, x3

    #MHPMCOUNTER21 read value
    csrr x14, 0xb15

    ##########################
    #MHPMCOUNTERH13 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1d} 
    ##########################
    #MHPMCOUNTERH13 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb8d, x3
    li x3, 0x1f
    csrrs x14, 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb8d, x3
    li x3, 0x0
    csrrs x14, 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb8d, x3
    li x3, 0x15
    csrrs x14, 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb8d, x3
    li x3, 0xa
    csrrs x14, 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    #MHPMCOUNTERH13 Write clear/set value 0x1d
    li x3, 0xffffffe2
    csrrc x14, 0xb8d, x3
    li x3, 0x1d
    csrrs x14, 0xb8d, x3

    #MHPMCOUNTERH13 read value
    csrr x14, 0xb8d

    ##########################
    #PMPCFG0 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #PMPCFG0 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3a0, x3
    li x3, 0x1f
    csrrs x14, 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3a0, x3
    li x3, 0x0
    csrrs x14, 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3a0, x3
    li x3, 0x15
    csrrs x14, 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3a0, x3
    li x3, 0xa
    csrrs x14, 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    #PMPCFG0 Write clear/set value 0xd
    li x3, 0xfffffff2
    csrrc x14, 0x3a0, x3
    li x3, 0xd
    csrrs x14, 0x3a0, x3

    #PMPCFG0 read value
    csrr x14, 0x3a0

    ##########################
    #MHPMCOUNTER12 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h11} 
    ##########################
    #MHPMCOUNTER12 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb0c, x3
    li x3, 0x1f
    csrrs x14, 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb0c, x3
    li x3, 0x0
    csrrs x14, 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb0c, x3
    li x3, 0x15
    csrrs x14, 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb0c, x3
    li x3, 0xa
    csrrs x14, 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    #MHPMCOUNTER12 Write clear/set value 0x11
    li x3, 0xffffffee
    csrrc x14, 0xb0c, x3
    li x3, 0x11
    csrrs x14, 0xb0c, x3

    #MHPMCOUNTER12 read value
    csrr x14, 0xb0c

    ##########################
    #MSTATUS testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1c} 
    ##########################
    #MSTATUS Write clear/set value 0x1f
    li x3, 0x7ffe19e0
    csrrc x14, 0x300, x3
    li x3, 0x1f
    csrrs x14, 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x0
    li x3, 0x7ffe19ff
    csrrc x14, 0x300, x3
    li x3, 0x0
    csrrs x14, 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x15
    li x3, 0x7ffe19ea
    csrrc x14, 0x300, x3
    li x3, 0x15
    csrrs x14, 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0xa
    li x3, 0x7ffe19f5
    csrrc x14, 0x300, x3
    li x3, 0xa
    csrrs x14, 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    #MSTATUS Write clear/set value 0x1c
    li x3, 0x7ffe19e3
    csrrc x14, 0x300, x3
    li x3, 0x1c
    csrrs x14, 0x300, x3

    #MSTATUS read value
    csrr x14, 0x300

    ##########################
    #MHPMCOUNTERH19 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #MHPMCOUNTERH19 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb93, x3
    li x3, 0x1f
    csrrs x14, 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb93, x3
    li x3, 0x0
    csrrs x14, 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb93, x3
    li x3, 0x15
    csrrs x14, 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb93, x3
    li x3, 0xa
    csrrs x14, 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    #MHPMCOUNTERH19 Write clear/set value 0x1
    li x3, 0xfffffffe
    csrrc x14, 0xb93, x3
    li x3, 0x1
    csrrs x14, 0xb93, x3

    #MHPMCOUNTERH19 read value
    csrr x14, 0xb93

    ##########################
    #MHPMEVENT19 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h14} 
    ##########################
    #MHPMEVENT19 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x333, x3
    li x3, 0x1f
    csrrs x14, 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x333, x3
    li x3, 0x0
    csrrs x14, 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x333, x3
    li x3, 0x15
    csrrs x14, 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x333, x3
    li x3, 0xa
    csrrs x14, 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    #MHPMEVENT19 Write clear/set value 0x14
    li x3, 0xffffffeb
    csrrc x14, 0x333, x3
    li x3, 0x14
    csrrs x14, 0x333, x3

    #MHPMEVENT19 read value
    csrr x14, 0x333

    ##########################
    #MHPMEVENT12 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'he} 
    ##########################
    #MHPMEVENT12 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x32c, x3
    li x3, 0x1f
    csrrs x14, 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x32c, x3
    li x3, 0x0
    csrrs x14, 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x32c, x3
    li x3, 0x15
    csrrs x14, 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x32c, x3
    li x3, 0xa
    csrrs x14, 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    #MHPMEVENT12 Write clear/set value 0xe
    li x3, 0xfffffff1
    csrrc x14, 0x32c, x3
    li x3, 0xe
    csrrs x14, 0x32c, x3

    #MHPMEVENT12 read value
    csrr x14, 0x32c

    ##########################
    #MHPMEVENT24 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h11} 
    ##########################
    #MHPMEVENT24 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x338, x3
    li x3, 0x1f
    csrrs x14, 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x338, x3
    li x3, 0x0
    csrrs x14, 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x338, x3
    li x3, 0x15
    csrrs x14, 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x338, x3
    li x3, 0xa
    csrrs x14, 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    #MHPMEVENT24 Write clear/set value 0x11
    li x3, 0xffffffee
    csrrc x14, 0x338, x3
    li x3, 0x11
    csrrs x14, 0x338, x3

    #MHPMEVENT24 read value
    csrr x14, 0x338

    ##########################
    #PMPCFG3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h0} 
    ##########################
    #PMPCFG3 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3a3, x3
    li x3, 0x1f
    csrrs x14, 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3a3, x3
    li x3, 0x0
    csrrs x14, 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3a3, x3
    li x3, 0x15
    csrrs x14, 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3a3, x3
    li x3, 0xa
    csrrs x14, 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    #PMPCFG3 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3a3, x3
    li x3, 0x0
    csrrs x14, 0x3a3, x3

    #PMPCFG3 read value
    csrr x14, 0x3a3

    ##########################
    #MHPMCOUNTER30 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h11} 
    ##########################
    #MHPMCOUNTER30 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb1e, x3
    li x3, 0x1f
    csrrs x14, 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb1e, x3
    li x3, 0x0
    csrrs x14, 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb1e, x3
    li x3, 0x15
    csrrs x14, 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb1e, x3
    li x3, 0xa
    csrrs x14, 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    #MHPMCOUNTER30 Write clear/set value 0x11
    li x3, 0xffffffee
    csrrc x14, 0xb1e, x3
    li x3, 0x11
    csrrs x14, 0xb1e, x3

    #MHPMCOUNTER30 read value
    csrr x14, 0xb1e

    ##########################
    #PMPADDR4 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hb} 
    ##########################
    #PMPADDR4 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b4, x3
    li x3, 0x1f
    csrrs x14, 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b4, x3
    li x3, 0x0
    csrrs x14, 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b4, x3
    li x3, 0x15
    csrrs x14, 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b4, x3
    li x3, 0xa
    csrrs x14, 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #PMPADDR4 Write clear/set value 0xb
    li x3, 0xfffffff4
    csrrc x14, 0x3b4, x3
    li x3, 0xb
    csrrs x14, 0x3b4, x3

    #PMPADDR4 read value
    csrr x14, 0x3b4

    #INSTRETH WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTER13 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1d} 
    ##########################
    #MHPMCOUNTER13 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb0d, x3
    li x3, 0x1f
    csrrs x14, 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb0d, x3
    li x3, 0x0
    csrrs x14, 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb0d, x3
    li x3, 0x15
    csrrs x14, 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb0d, x3
    li x3, 0xa
    csrrs x14, 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    #MHPMCOUNTER13 Write clear/set value 0x1d
    li x3, 0xffffffe2
    csrrc x14, 0xb0d, x3
    li x3, 0x1d
    csrrs x14, 0xb0d, x3

    #MHPMCOUNTER13 read value
    csrr x14, 0xb0d

    ##########################
    #MHPMCOUNTER8 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #MHPMCOUNTER8 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb08, x3
    li x3, 0x1f
    csrrs x14, 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb08, x3
    li x3, 0x0
    csrrs x14, 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb08, x3
    li x3, 0x15
    csrrs x14, 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb08, x3
    li x3, 0xa
    csrrs x14, 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    #MHPMCOUNTER8 Write clear/set value 0x1
    li x3, 0xfffffffe
    csrrc x14, 0xb08, x3
    li x3, 0x1
    csrrs x14, 0xb08, x3

    #MHPMCOUNTER8 read value
    csrr x14, 0xb08

    ##########################
    #ICACHE testing W/R values '{'h1e, 'h1, 'h15, 'ha, 'h6} 
    ##########################
    #ICACHE Write clear/set value 0x1e
    li x3, 0xffffffe1
    csrrc x14, 0x7c0, x3
    li x3, 0x1e
    csrrs x14, 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write clear/set value 0x1
    li x3, 0xfffffffe
    csrrc x14, 0x7c0, x3
    li x3, 0x1
    csrrs x14, 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x7c0, x3
    li x3, 0x15
    csrrs x14, 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x7c0, x3
    li x3, 0xa
    csrrs x14, 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    #ICACHE Write clear/set value 0x6
    li x3, 0xfffffff9
    csrrc x14, 0x7c0, x3
    li x3, 0x6
    csrrs x14, 0x7c0, x3

    #ICACHE read value
    csrr x14, 0x7c0

    ##########################
    #MSCRATCH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1c} 
    ##########################
    #MSCRATCH Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x340, x3
    li x3, 0x1f
    csrrs x14, 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x340, x3
    li x3, 0x0
    csrrs x14, 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x340, x3
    li x3, 0x15
    csrrs x14, 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x340, x3
    li x3, 0xa
    csrrs x14, 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    #MSCRATCH Write clear/set value 0x1c
    li x3, 0xffffffe3
    csrrc x14, 0x340, x3
    li x3, 0x1c
    csrrs x14, 0x340, x3

    #MSCRATCH read value
    csrr x14, 0x340

    ##########################
    #MHPMCOUNTER15 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h3} 
    ##########################
    #MHPMCOUNTER15 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb0f, x3
    li x3, 0x1f
    csrrs x14, 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb0f, x3
    li x3, 0x0
    csrrs x14, 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb0f, x3
    li x3, 0x15
    csrrs x14, 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb0f, x3
    li x3, 0xa
    csrrs x14, 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    #MHPMCOUNTER15 Write clear/set value 0x3
    li x3, 0xfffffffc
    csrrc x14, 0xb0f, x3
    li x3, 0x3
    csrrs x14, 0xb0f, x3

    #MHPMCOUNTER15 read value
    csrr x14, 0xb0f

    ##########################
    #MHPMEVENT13 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h13} 
    ##########################
    #MHPMEVENT13 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x32d, x3
    li x3, 0x1f
    csrrs x14, 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x32d, x3
    li x3, 0x0
    csrrs x14, 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x32d, x3
    li x3, 0x15
    csrrs x14, 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x32d, x3
    li x3, 0xa
    csrrs x14, 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    #MHPMEVENT13 Write clear/set value 0x13
    li x3, 0xffffffec
    csrrc x14, 0x32d, x3
    li x3, 0x13
    csrrs x14, 0x32d, x3

    #MHPMEVENT13 read value
    csrr x14, 0x32d

    ##########################
    #PMPADDR0 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7} 
    ##########################
    #PMPADDR0 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b0, x3
    li x3, 0x1f
    csrrs x14, 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b0, x3
    li x3, 0x0
    csrrs x14, 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b0, x3
    li x3, 0x15
    csrrs x14, 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b0, x3
    li x3, 0xa
    csrrs x14, 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    #PMPADDR0 Write clear/set value 0x7
    li x3, 0xfffffff8
    csrrc x14, 0x3b0, x3
    li x3, 0x7
    csrrs x14, 0x3b0, x3

    #PMPADDR0 read value
    csrr x14, 0x3b0

    ##########################
    #MHPMCOUNTER31 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h14} 
    ##########################
    #MHPMCOUNTER31 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb1f, x3
    li x3, 0x1f
    csrrs x14, 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb1f, x3
    li x3, 0x0
    csrrs x14, 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb1f, x3
    li x3, 0x15
    csrrs x14, 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb1f, x3
    li x3, 0xa
    csrrs x14, 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    #MHPMCOUNTER31 Write clear/set value 0x14
    li x3, 0xffffffeb
    csrrc x14, 0xb1f, x3
    li x3, 0x14
    csrrs x14, 0xb1f, x3

    #MHPMCOUNTER31 read value
    csrr x14, 0xb1f

    ##########################
    #MHPMCOUNTER11 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7} 
    ##########################
    #MHPMCOUNTER11 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb0b, x3
    li x3, 0x1f
    csrrs x14, 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb0b, x3
    li x3, 0x0
    csrrs x14, 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb0b, x3
    li x3, 0x15
    csrrs x14, 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb0b, x3
    li x3, 0xa
    csrrs x14, 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    #MHPMCOUNTER11 Write clear/set value 0x7
    li x3, 0xfffffff8
    csrrc x14, 0xb0b, x3
    li x3, 0x7
    csrrs x14, 0xb0b, x3

    #MHPMCOUNTER11 read value
    csrr x14, 0xb0b

    ##########################
    #MHPMEVENT11 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1b} 
    ##########################
    #MHPMEVENT11 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x32b, x3
    li x3, 0x1f
    csrrs x14, 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x32b, x3
    li x3, 0x0
    csrrs x14, 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x32b, x3
    li x3, 0x15
    csrrs x14, 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x32b, x3
    li x3, 0xa
    csrrs x14, 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    #MHPMEVENT11 Write clear/set value 0x1b
    li x3, 0xffffffe4
    csrrc x14, 0x32b, x3
    li x3, 0x1b
    csrrs x14, 0x32b, x3

    #MHPMEVENT11 read value
    csrr x14, 0x32b

    ##########################
    #MHPMCOUNTERH21 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1b} 
    ##########################
    #MHPMCOUNTERH21 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb95, x3
    li x3, 0x1f
    csrrs x14, 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb95, x3
    li x3, 0x0
    csrrs x14, 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb95, x3
    li x3, 0x15
    csrrs x14, 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb95, x3
    li x3, 0xa
    csrrs x14, 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    #MHPMCOUNTERH21 Write clear/set value 0x1b
    li x3, 0xffffffe4
    csrrc x14, 0xb95, x3
    li x3, 0x1b
    csrrs x14, 0xb95, x3

    #MHPMCOUNTERH21 read value
    csrr x14, 0xb95

    ##########################
    #PMPADDR3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h13} 
    ##########################
    #PMPADDR3 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b3, x3
    li x3, 0x1f
    csrrs x14, 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b3, x3
    li x3, 0x0
    csrrs x14, 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b3, x3
    li x3, 0x15
    csrrs x14, 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b3, x3
    li x3, 0xa
    csrrs x14, 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    #PMPADDR3 Write clear/set value 0x13
    li x3, 0xffffffec
    csrrc x14, 0x3b3, x3
    li x3, 0x13
    csrrs x14, 0x3b3, x3

    #PMPADDR3 read value
    csrr x14, 0x3b3

    ##########################
    #MHPMEVENT28 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMEVENT28 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x33c, x3
    li x3, 0x1f
    csrrs x14, 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x33c, x3
    li x3, 0x0
    csrrs x14, 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x33c, x3
    li x3, 0x15
    csrrs x14, 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x33c, x3
    li x3, 0xa
    csrrs x14, 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    #MHPMEVENT28 Write clear/set value 0x2
    li x3, 0xfffffffd
    csrrc x14, 0x33c, x3
    li x3, 0x2
    csrrs x14, 0x33c, x3

    #MHPMEVENT28 read value
    csrr x14, 0x33c

    ##########################
    #MHPMCOUNTER9 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7} 
    ##########################
    #MHPMCOUNTER9 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb09, x3
    li x3, 0x1f
    csrrs x14, 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb09, x3
    li x3, 0x0
    csrrs x14, 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb09, x3
    li x3, 0x15
    csrrs x14, 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb09, x3
    li x3, 0xa
    csrrs x14, 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    #MHPMCOUNTER9 Write clear/set value 0x7
    li x3, 0xfffffff8
    csrrc x14, 0xb09, x3
    li x3, 0x7
    csrrs x14, 0xb09, x3

    #MHPMCOUNTER9 read value
    csrr x14, 0xb09

    ##########################
    #PMPADDR15 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f} 
    ##########################
    #PMPADDR15 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3bf, x3
    li x3, 0x1f
    csrrs x14, 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3bf, x3
    li x3, 0x0
    csrrs x14, 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3bf, x3
    li x3, 0x15
    csrrs x14, 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3bf, x3
    li x3, 0xa
    csrrs x14, 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    #PMPADDR15 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3bf, x3
    li x3, 0x1f
    csrrs x14, 0x3bf, x3

    #PMPADDR15 read value
    csrr x14, 0x3bf

    ##########################
    #MHPMCOUNTERH22 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h8} 
    ##########################
    #MHPMCOUNTERH22 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb96, x3
    li x3, 0x1f
    csrrs x14, 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb96, x3
    li x3, 0x0
    csrrs x14, 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb96, x3
    li x3, 0x15
    csrrs x14, 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb96, x3
    li x3, 0xa
    csrrs x14, 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    #MHPMCOUNTERH22 Write clear/set value 0x8
    li x3, 0xfffffff7
    csrrc x14, 0xb96, x3
    li x3, 0x8
    csrrs x14, 0xb96, x3

    #MHPMCOUNTERH22 read value
    csrr x14, 0xb96

    ##########################
    #PMPADDR13 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a} 
    ##########################
    #PMPADDR13 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3bd, x3
    li x3, 0x1f
    csrrs x14, 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3bd, x3
    li x3, 0x0
    csrrs x14, 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3bd, x3
    li x3, 0x15
    csrrs x14, 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3bd, x3
    li x3, 0xa
    csrrs x14, 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    #PMPADDR13 Write clear/set value 0x1a
    li x3, 0xffffffe5
    csrrc x14, 0x3bd, x3
    li x3, 0x1a
    csrrs x14, 0x3bd, x3

    #PMPADDR13 read value
    csrr x14, 0x3bd

    ##########################
    #MHPMCOUNTER17 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'he} 
    ##########################
    #MHPMCOUNTER17 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb11, x3
    li x3, 0x1f
    csrrs x14, 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb11, x3
    li x3, 0x0
    csrrs x14, 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb11, x3
    li x3, 0x15
    csrrs x14, 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb11, x3
    li x3, 0xa
    csrrs x14, 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    #MHPMCOUNTER17 Write clear/set value 0xe
    li x3, 0xfffffff1
    csrrc x14, 0xb11, x3
    li x3, 0xe
    csrrs x14, 0xb11, x3

    #MHPMCOUNTER17 read value
    csrr x14, 0xb11

    ##########################
    #MHPMEVENT3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #MHPMEVENT3 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x323, x3
    li x3, 0x1f
    csrrs x14, 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x323, x3
    li x3, 0x0
    csrrs x14, 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x323, x3
    li x3, 0x15
    csrrs x14, 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x323, x3
    li x3, 0xa
    csrrs x14, 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    #MHPMEVENT3 Write clear/set value 0x2
    li x3, 0xfffffffd
    csrrc x14, 0x323, x3
    li x3, 0x2
    csrrs x14, 0x323, x3

    #MHPMEVENT3 read value
    csrr x14, 0x323

    ##########################
    #MCYCLE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'ha} 
    ##########################
    #MCYCLE Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb00, x3
    li x3, 0x1f
    csrrs x14, 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb00, x3
    li x3, 0x0
    csrrs x14, 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb00, x3
    li x3, 0x15
    csrrs x14, 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb00, x3
    li x3, 0xa
    csrrs x14, 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #MCYCLE Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb00, x3
    li x3, 0xa
    csrrs x14, 0xb00, x3

    #MCYCLE read value
    csrr x14, 0xb00

    #CYCLEH WR skipped since it's a RO register

    #MARCHID WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTERH20 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hf} 
    ##########################
    #MHPMCOUNTERH20 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb94, x3
    li x3, 0x1f
    csrrs x14, 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb94, x3
    li x3, 0x0
    csrrs x14, 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb94, x3
    li x3, 0x15
    csrrs x14, 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb94, x3
    li x3, 0xa
    csrrs x14, 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    #MHPMCOUNTERH20 Write clear/set value 0xf
    li x3, 0xfffffff0
    csrrc x14, 0xb94, x3
    li x3, 0xf
    csrrs x14, 0xb94, x3

    #MHPMCOUNTERH20 read value
    csrr x14, 0xb94

    ##########################
    #MHPMCOUNTER3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h14} 
    ##########################
    #MHPMCOUNTER3 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb03, x3
    li x3, 0x1f
    csrrs x14, 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb03, x3
    li x3, 0x0
    csrrs x14, 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb03, x3
    li x3, 0x15
    csrrs x14, 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb03, x3
    li x3, 0xa
    csrrs x14, 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    #MHPMCOUNTER3 Write clear/set value 0x14
    li x3, 0xffffffeb
    csrrc x14, 0xb03, x3
    li x3, 0x14
    csrrs x14, 0xb03, x3

    #MHPMCOUNTER3 read value
    csrr x14, 0xb03

    ##########################
    #MHPMCOUNTER26 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #MHPMCOUNTER26 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb1a, x3
    li x3, 0x1f
    csrrs x14, 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb1a, x3
    li x3, 0x0
    csrrs x14, 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb1a, x3
    li x3, 0x15
    csrrs x14, 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb1a, x3
    li x3, 0xa
    csrrs x14, 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    #MHPMCOUNTER26 Write clear/set value 0x10
    li x3, 0xffffffef
    csrrc x14, 0xb1a, x3
    li x3, 0x10
    csrrs x14, 0xb1a, x3

    #MHPMCOUNTER26 read value
    csrr x14, 0xb1a

    ##########################
    #MTVEC testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h17} 
    ##########################
    #MTVEC Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x305, x3
    li x3, 0x1f
    csrrs x14, 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x305, x3
    li x3, 0x0
    csrrs x14, 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x305, x3
    li x3, 0x15
    csrrs x14, 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x305, x3
    li x3, 0xa
    csrrs x14, 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    #MTVEC Write clear/set value 0x17
    li x3, 0xffffffe8
    csrrc x14, 0x305, x3
    li x3, 0x17
    csrrs x14, 0x305, x3

    #MTVEC read value
    csrr x14, 0x305

    ##########################
    #MHPMCOUNTERH18 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hf} 
    ##########################
    #MHPMCOUNTERH18 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb92, x3
    li x3, 0x1f
    csrrs x14, 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb92, x3
    li x3, 0x0
    csrrs x14, 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb92, x3
    li x3, 0x15
    csrrs x14, 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb92, x3
    li x3, 0xa
    csrrs x14, 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    #MHPMCOUNTERH18 Write clear/set value 0xf
    li x3, 0xfffffff0
    csrrc x14, 0xb92, x3
    li x3, 0xf
    csrrs x14, 0xb92, x3

    #MHPMCOUNTERH18 read value
    csrr x14, 0xb92

    ##########################
    #MHPMCOUNTERH30 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #MHPMCOUNTERH30 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb9e, x3
    li x3, 0x1f
    csrrs x14, 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb9e, x3
    li x3, 0x0
    csrrs x14, 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb9e, x3
    li x3, 0x15
    csrrs x14, 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb9e, x3
    li x3, 0xa
    csrrs x14, 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MHPMCOUNTERH30 Write clear/set value 0x19
    li x3, 0xffffffe6
    csrrc x14, 0xb9e, x3
    li x3, 0x19
    csrrs x14, 0xb9e, x3

    #MHPMCOUNTERH30 read value
    csrr x14, 0xb9e

    #MVENDORID WR skipped since it's a RO register

    ##########################
    #MHPMEVENT26 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #MHPMEVENT26 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x33a, x3
    li x3, 0x1f
    csrrs x14, 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x33a, x3
    li x3, 0x0
    csrrs x14, 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x33a, x3
    li x3, 0x15
    csrrs x14, 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x33a, x3
    li x3, 0xa
    csrrs x14, 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    #MHPMEVENT26 Write clear/set value 0x18
    li x3, 0xffffffe7
    csrrc x14, 0x33a, x3
    li x3, 0x18
    csrrs x14, 0x33a, x3

    #MHPMEVENT26 read value
    csrr x14, 0x33a

    ##########################
    #MCAUSE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #MCAUSE Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x342, x3
    li x3, 0x1f
    csrrs x14, 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x342, x3
    li x3, 0x0
    csrrs x14, 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x342, x3
    li x3, 0x15
    csrrs x14, 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x342, x3
    li x3, 0xa
    csrrs x14, 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    #MCAUSE Write clear/set value 0x1
    li x3, 0xfffffffe
    csrrc x14, 0x342, x3
    li x3, 0x1
    csrrs x14, 0x342, x3

    #MCAUSE read value
    csrr x14, 0x342

    ##########################
    #MINSTRETH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7} 
    ##########################
    #MINSTRETH Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb82, x3
    li x3, 0x1f
    csrrs x14, 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb82, x3
    li x3, 0x0
    csrrs x14, 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb82, x3
    li x3, 0x15
    csrrs x14, 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb82, x3
    li x3, 0xa
    csrrs x14, 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    #MINSTRETH Write clear/set value 0x7
    li x3, 0xfffffff8
    csrrc x14, 0xb82, x3
    li x3, 0x7
    csrrs x14, 0xb82, x3

    #MINSTRETH read value
    csrr x14, 0xb82

    ##########################
    #MHPMCOUNTER16 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1d} 
    ##########################
    #MHPMCOUNTER16 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb10, x3
    li x3, 0x1f
    csrrs x14, 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb10, x3
    li x3, 0x0
    csrrs x14, 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb10, x3
    li x3, 0x15
    csrrs x14, 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb10, x3
    li x3, 0xa
    csrrs x14, 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    #MHPMCOUNTER16 Write clear/set value 0x1d
    li x3, 0xffffffe2
    csrrc x14, 0xb10, x3
    li x3, 0x1d
    csrrs x14, 0xb10, x3

    #MHPMCOUNTER16 read value
    csrr x14, 0xb10

    ##########################
    #PMPADDR7 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #PMPADDR7 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b7, x3
    li x3, 0x1f
    csrrs x14, 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b7, x3
    li x3, 0x0
    csrrs x14, 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b7, x3
    li x3, 0x15
    csrrs x14, 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b7, x3
    li x3, 0xa
    csrrs x14, 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    #PMPADDR7 Write clear/set value 0x18
    li x3, 0xffffffe7
    csrrc x14, 0x3b7, x3
    li x3, 0x18
    csrrs x14, 0x3b7, x3

    #PMPADDR7 read value
    csrr x14, 0x3b7

    ##########################
    #MHPMCOUNTERH24 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'he} 
    ##########################
    #MHPMCOUNTERH24 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb98, x3
    li x3, 0x1f
    csrrs x14, 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb98, x3
    li x3, 0x0
    csrrs x14, 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb98, x3
    li x3, 0x15
    csrrs x14, 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb98, x3
    li x3, 0xa
    csrrs x14, 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    #MHPMCOUNTERH24 Write clear/set value 0xe
    li x3, 0xfffffff1
    csrrc x14, 0xb98, x3
    li x3, 0xe
    csrrs x14, 0xb98, x3

    #MHPMCOUNTERH24 read value
    csrr x14, 0xb98

    ##########################
    #PMPADDR12 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1b} 
    ##########################
    #PMPADDR12 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3bc, x3
    li x3, 0x1f
    csrrs x14, 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3bc, x3
    li x3, 0x0
    csrrs x14, 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3bc, x3
    li x3, 0x15
    csrrs x14, 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3bc, x3
    li x3, 0xa
    csrrs x14, 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    #PMPADDR12 Write clear/set value 0x1b
    li x3, 0xffffffe4
    csrrc x14, 0x3bc, x3
    li x3, 0x1b
    csrrs x14, 0x3bc, x3

    #PMPADDR12 read value
    csrr x14, 0x3bc

    ##########################
    #MIP testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7} 
    ##########################
    #MIP Write clear/set value 0x1f
    li x3, 0xfffff760
    csrrc x14, 0x344, x3
    li x3, 0x1f
    csrrs x14, 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write clear/set value 0x0
    li x3, 0xfffff777
    csrrc x14, 0x344, x3
    li x3, 0x0
    csrrs x14, 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write clear/set value 0x15
    li x3, 0xfffff762
    csrrc x14, 0x344, x3
    li x3, 0x15
    csrrs x14, 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write clear/set value 0xa
    li x3, 0xfffff775
    csrrc x14, 0x344, x3
    li x3, 0xa
    csrrs x14, 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #MIP Write clear/set value 0x7
    li x3, 0xfffff770
    csrrc x14, 0x344, x3
    li x3, 0x7
    csrrs x14, 0x344, x3

    #MIP read value
    csrr x14, 0x344

    #Clear MIP to avoid traping
    csrw 0x344, x0

    #MIP read value
    csrr x14, 0x344

    ##########################
    #MHPMCOUNTERH9 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'ha} 
    ##########################
    #MHPMCOUNTERH9 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb89, x3
    li x3, 0x1f
    csrrs x14, 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb89, x3
    li x3, 0x0
    csrrs x14, 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb89, x3
    li x3, 0x15
    csrrs x14, 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb89, x3
    li x3, 0xa
    csrrs x14, 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    #MHPMCOUNTERH9 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb89, x3
    li x3, 0xa
    csrrs x14, 0xb89, x3

    #MHPMCOUNTERH9 read value
    csrr x14, 0xb89

    ##########################
    #MHPMCOUNTER28 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hf} 
    ##########################
    #MHPMCOUNTER28 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb1c, x3
    li x3, 0x1f
    csrrs x14, 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb1c, x3
    li x3, 0x0
    csrrs x14, 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb1c, x3
    li x3, 0x15
    csrrs x14, 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb1c, x3
    li x3, 0xa
    csrrs x14, 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    #MHPMCOUNTER28 Write clear/set value 0xf
    li x3, 0xfffffff0
    csrrc x14, 0xb1c, x3
    li x3, 0xf
    csrrs x14, 0xb1c, x3

    #MHPMCOUNTER28 read value
    csrr x14, 0xb1c

    ##########################
    #MHPMCOUNTERH7 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h14} 
    ##########################
    #MHPMCOUNTERH7 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb87, x3
    li x3, 0x1f
    csrrs x14, 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb87, x3
    li x3, 0x0
    csrrs x14, 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb87, x3
    li x3, 0x15
    csrrs x14, 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb87, x3
    li x3, 0xa
    csrrs x14, 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    #MHPMCOUNTERH7 Write clear/set value 0x14
    li x3, 0xffffffeb
    csrrc x14, 0xb87, x3
    li x3, 0x14
    csrrs x14, 0xb87, x3

    #MHPMCOUNTERH7 read value
    csrr x14, 0xb87

    ##########################
    #MHPMEVENT21 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1e} 
    ##########################
    #MHPMEVENT21 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x335, x3
    li x3, 0x1f
    csrrs x14, 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x335, x3
    li x3, 0x0
    csrrs x14, 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x335, x3
    li x3, 0x15
    csrrs x14, 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x335, x3
    li x3, 0xa
    csrrs x14, 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    #MHPMEVENT21 Write clear/set value 0x1e
    li x3, 0xffffffe1
    csrrc x14, 0x335, x3
    li x3, 0x1e
    csrrs x14, 0x335, x3

    #MHPMEVENT21 read value
    csrr x14, 0x335

    ##########################
    #MHPMEVENT31 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h8} 
    ##########################
    #MHPMEVENT31 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x33f, x3
    li x3, 0x1f
    csrrs x14, 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x33f, x3
    li x3, 0x0
    csrrs x14, 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x33f, x3
    li x3, 0x15
    csrrs x14, 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x33f, x3
    li x3, 0xa
    csrrs x14, 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    #MHPMEVENT31 Write clear/set value 0x8
    li x3, 0xfffffff7
    csrrc x14, 0x33f, x3
    li x3, 0x8
    csrrs x14, 0x33f, x3

    #MHPMEVENT31 read value
    csrr x14, 0x33f

    ##########################
    #PMPADDR10 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'ha} 
    ##########################
    #PMPADDR10 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3ba, x3
    li x3, 0x1f
    csrrs x14, 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3ba, x3
    li x3, 0x0
    csrrs x14, 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3ba, x3
    li x3, 0x15
    csrrs x14, 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3ba, x3
    li x3, 0xa
    csrrs x14, 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    #PMPADDR10 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3ba, x3
    li x3, 0xa
    csrrs x14, 0x3ba, x3

    #PMPADDR10 read value
    csrr x14, 0x3ba

    ##########################
    #PMPCFG2 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hc} 
    ##########################
    #PMPCFG2 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3a2, x3
    li x3, 0x1f
    csrrs x14, 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3a2, x3
    li x3, 0x0
    csrrs x14, 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3a2, x3
    li x3, 0x15
    csrrs x14, 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3a2, x3
    li x3, 0xa
    csrrs x14, 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    #PMPCFG2 Write clear/set value 0xc
    li x3, 0xfffffff3
    csrrc x14, 0x3a2, x3
    li x3, 0xc
    csrrs x14, 0x3a2, x3

    #PMPCFG2 read value
    csrr x14, 0x3a2

    ##########################
    #MISA testing W/R values '{'h1b, 'h4, 'h15, 'ha, 'hc} 
    ##########################
    #MISA Write clear/set value 0x1b
    li x3, 0xffffffe4
    csrrc x14, 0x301, x3
    li x3, 0x1b
    csrrs x14, 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write clear/set value 0x4
    li x3, 0xfffffffb
    csrrc x14, 0x301, x3
    li x3, 0x4
    csrrs x14, 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x301, x3
    li x3, 0x15
    csrrs x14, 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x301, x3
    li x3, 0xa
    csrrs x14, 0x301, x3

    #MISA read value
    csrr x14, 0x301

    #MISA Write clear/set value 0xc
    li x3, 0xfffffff3
    csrrc x14, 0x301, x3
    li x3, 0xc
    csrrs x14, 0x301, x3

    #MISA read value
    csrr x14, 0x301

    ##########################
    #PMPADDR2 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h10} 
    ##########################
    #PMPADDR2 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b2, x3
    li x3, 0x1f
    csrrs x14, 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b2, x3
    li x3, 0x0
    csrrs x14, 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b2, x3
    li x3, 0x15
    csrrs x14, 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b2, x3
    li x3, 0xa
    csrrs x14, 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    #PMPADDR2 Write clear/set value 0x10
    li x3, 0xffffffef
    csrrc x14, 0x3b2, x3
    li x3, 0x10
    csrrs x14, 0x3b2, x3

    #PMPADDR2 read value
    csrr x14, 0x3b2

    ##########################
    #MHPMCOUNTERH31 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hb} 
    ##########################
    #MHPMCOUNTERH31 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb9f, x3
    li x3, 0x1f
    csrrs x14, 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb9f, x3
    li x3, 0x0
    csrrs x14, 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb9f, x3
    li x3, 0x15
    csrrs x14, 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb9f, x3
    li x3, 0xa
    csrrs x14, 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    #MHPMCOUNTERH31 Write clear/set value 0xb
    li x3, 0xfffffff4
    csrrc x14, 0xb9f, x3
    li x3, 0xb
    csrrs x14, 0xb9f, x3

    #MHPMCOUNTERH31 read value
    csrr x14, 0xb9f

    ##########################
    #MSTATUSH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h5} 
    ##########################
    #MSTATUSH Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x310, x3
    li x3, 0x1f
    csrrs x14, 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x310, x3
    li x3, 0x0
    csrrs x14, 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x310, x3
    li x3, 0x15
    csrrs x14, 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x310, x3
    li x3, 0xa
    csrrs x14, 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    #MSTATUSH Write clear/set value 0x5
    li x3, 0xfffffffa
    csrrc x14, 0x310, x3
    li x3, 0x5
    csrrs x14, 0x310, x3

    #MSTATUSH read value
    csrr x14, 0x310

    ##########################
    #MHPMEVENT6 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h9} 
    ##########################
    #MHPMEVENT6 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x326, x3
    li x3, 0x1f
    csrrs x14, 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x326, x3
    li x3, 0x0
    csrrs x14, 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x326, x3
    li x3, 0x15
    csrrs x14, 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x326, x3
    li x3, 0xa
    csrrs x14, 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    #MHPMEVENT6 Write clear/set value 0x9
    li x3, 0xfffffff6
    csrrc x14, 0x326, x3
    li x3, 0x9
    csrrs x14, 0x326, x3

    #MHPMEVENT6 read value
    csrr x14, 0x326

    ##########################
    #MHPMCOUNTERH14 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h3} 
    ##########################
    #MHPMCOUNTERH14 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb8e, x3
    li x3, 0x1f
    csrrs x14, 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb8e, x3
    li x3, 0x0
    csrrs x14, 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb8e, x3
    li x3, 0x15
    csrrs x14, 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb8e, x3
    li x3, 0xa
    csrrs x14, 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    #MHPMCOUNTERH14 Write clear/set value 0x3
    li x3, 0xfffffffc
    csrrc x14, 0xb8e, x3
    li x3, 0x3
    csrrs x14, 0xb8e, x3

    #MHPMCOUNTERH14 read value
    csrr x14, 0xb8e

    ##########################
    #PMPADDR9 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #PMPADDR9 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b9, x3
    li x3, 0x1f
    csrrs x14, 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b9, x3
    li x3, 0x0
    csrrs x14, 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b9, x3
    li x3, 0x15
    csrrs x14, 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b9, x3
    li x3, 0xa
    csrrs x14, 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    #PMPADDR9 Write clear/set value 0x19
    li x3, 0xffffffe6
    csrrc x14, 0x3b9, x3
    li x3, 0x19
    csrrs x14, 0x3b9, x3

    #PMPADDR9 read value
    csrr x14, 0x3b9

    ##########################
    #PMPADDR14 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #PMPADDR14 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3be, x3
    li x3, 0x1f
    csrrs x14, 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3be, x3
    li x3, 0x0
    csrrs x14, 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3be, x3
    li x3, 0x15
    csrrs x14, 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3be, x3
    li x3, 0xa
    csrrs x14, 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    #PMPADDR14 Write clear/set value 0x19
    li x3, 0xffffffe6
    csrrc x14, 0x3be, x3
    li x3, 0x19
    csrrs x14, 0x3be, x3

    #PMPADDR14 read value
    csrr x14, 0x3be

    ##########################
    #MHPMCOUNTERH17 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1c} 
    ##########################
    #MHPMCOUNTERH17 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb91, x3
    li x3, 0x1f
    csrrs x14, 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb91, x3
    li x3, 0x0
    csrrs x14, 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb91, x3
    li x3, 0x15
    csrrs x14, 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb91, x3
    li x3, 0xa
    csrrs x14, 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    #MHPMCOUNTERH17 Write clear/set value 0x1c
    li x3, 0xffffffe3
    csrrc x14, 0xb91, x3
    li x3, 0x1c
    csrrs x14, 0xb91, x3

    #MHPMCOUNTERH17 read value
    csrr x14, 0xb91

    ##########################
    #MHPMCOUNTER24 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h6} 
    ##########################
    #MHPMCOUNTER24 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb18, x3
    li x3, 0x1f
    csrrs x14, 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb18, x3
    li x3, 0x0
    csrrs x14, 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb18, x3
    li x3, 0x15
    csrrs x14, 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb18, x3
    li x3, 0xa
    csrrs x14, 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    #MHPMCOUNTER24 Write clear/set value 0x6
    li x3, 0xfffffff9
    csrrc x14, 0xb18, x3
    li x3, 0x6
    csrrs x14, 0xb18, x3

    #MHPMCOUNTER24 read value
    csrr x14, 0xb18

    ##########################
    #MHPMEVENT7 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h0} 
    ##########################
    #MHPMEVENT7 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x327, x3
    li x3, 0x1f
    csrrs x14, 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x327, x3
    li x3, 0x0
    csrrs x14, 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x327, x3
    li x3, 0x15
    csrrs x14, 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x327, x3
    li x3, 0xa
    csrrs x14, 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    #MHPMEVENT7 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x327, x3
    li x3, 0x0
    csrrs x14, 0x327, x3

    #MHPMEVENT7 read value
    csrr x14, 0x327

    ##########################
    #MHPMCOUNTERH26 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #MHPMCOUNTERH26 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb9a, x3
    li x3, 0x1f
    csrrs x14, 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb9a, x3
    li x3, 0x0
    csrrs x14, 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb9a, x3
    li x3, 0x15
    csrrs x14, 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb9a, x3
    li x3, 0xa
    csrrs x14, 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    #MHPMCOUNTERH26 Write clear/set value 0xd
    li x3, 0xfffffff2
    csrrc x14, 0xb9a, x3
    li x3, 0xd
    csrrs x14, 0xb9a, x3

    #MHPMCOUNTERH26 read value
    csrr x14, 0xb9a

    ##########################
    #PMPCFG1 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #PMPCFG1 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3a1, x3
    li x3, 0x1f
    csrrs x14, 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3a1, x3
    li x3, 0x0
    csrrs x14, 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3a1, x3
    li x3, 0x15
    csrrs x14, 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3a1, x3
    li x3, 0xa
    csrrs x14, 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    #PMPCFG1 Write clear/set value 0x2
    li x3, 0xfffffffd
    csrrc x14, 0x3a1, x3
    li x3, 0x2
    csrrs x14, 0x3a1, x3

    #PMPCFG1 read value
    csrr x14, 0x3a1

    ##########################
    #MCYCLEH testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #MCYCLEH Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb80, x3
    li x3, 0x1f
    csrrs x14, 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb80, x3
    li x3, 0x0
    csrrs x14, 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb80, x3
    li x3, 0x15
    csrrs x14, 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb80, x3
    li x3, 0xa
    csrrs x14, 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    #MCYCLEH Write clear/set value 0xd
    li x3, 0xfffffff2
    csrrc x14, 0xb80, x3
    li x3, 0xd
    csrrs x14, 0xb80, x3

    #MCYCLEH read value
    csrr x14, 0xb80

    ##########################
    #MIE testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h15} 
    ##########################
    #MIE Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x304, x3
    li x3, 0x1f
    csrrs x14, 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x304, x3
    li x3, 0x0
    csrrs x14, 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x304, x3
    li x3, 0x15
    csrrs x14, 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x304, x3
    li x3, 0xa
    csrrs x14, 0x304, x3

    #MIE read value
    csrr x14, 0x304

    #MIE Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x304, x3
    li x3, 0x15
    csrrs x14, 0x304, x3

    #MIE read value
    csrr x14, 0x304

    ##########################
    #MHPMEVENT27 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #MHPMEVENT27 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x33b, x3
    li x3, 0x1f
    csrrs x14, 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x33b, x3
    li x3, 0x0
    csrrs x14, 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x33b, x3
    li x3, 0x15
    csrrs x14, 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x33b, x3
    li x3, 0xa
    csrrs x14, 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    #MHPMEVENT27 Write clear/set value 0x19
    li x3, 0xffffffe6
    csrrc x14, 0x33b, x3
    li x3, 0x19
    csrrs x14, 0x33b, x3

    #MHPMEVENT27 read value
    csrr x14, 0x33b

    ##########################
    #MHPMEVENT30 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h8} 
    ##########################
    #MHPMEVENT30 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x33e, x3
    li x3, 0x1f
    csrrs x14, 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x33e, x3
    li x3, 0x0
    csrrs x14, 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x33e, x3
    li x3, 0x15
    csrrs x14, 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x33e, x3
    li x3, 0xa
    csrrs x14, 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    #MHPMEVENT30 Write clear/set value 0x8
    li x3, 0xfffffff7
    csrrc x14, 0x33e, x3
    li x3, 0x8
    csrrs x14, 0x33e, x3

    #MHPMEVENT30 read value
    csrr x14, 0x33e

    ##########################
    #MHPMEVENT9 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hc} 
    ##########################
    #MHPMEVENT9 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x329, x3
    li x3, 0x1f
    csrrs x14, 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x329, x3
    li x3, 0x0
    csrrs x14, 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x329, x3
    li x3, 0x15
    csrrs x14, 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x329, x3
    li x3, 0xa
    csrrs x14, 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    #MHPMEVENT9 Write clear/set value 0xc
    li x3, 0xfffffff3
    csrrc x14, 0x329, x3
    li x3, 0xc
    csrrs x14, 0x329, x3

    #MHPMEVENT9 read value
    csrr x14, 0x329

    ##########################
    #MHPMCOUNTER14 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #MHPMCOUNTER14 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb0e, x3
    li x3, 0x1f
    csrrs x14, 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb0e, x3
    li x3, 0x0
    csrrs x14, 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb0e, x3
    li x3, 0x15
    csrrs x14, 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb0e, x3
    li x3, 0xa
    csrrs x14, 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    #MHPMCOUNTER14 Write clear/set value 0x1
    li x3, 0xfffffffe
    csrrc x14, 0xb0e, x3
    li x3, 0x1
    csrrs x14, 0xb0e, x3

    #MHPMCOUNTER14 read value
    csrr x14, 0xb0e

    ##########################
    #MHPMCOUNTER7 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h13} 
    ##########################
    #MHPMCOUNTER7 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb07, x3
    li x3, 0x1f
    csrrs x14, 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb07, x3
    li x3, 0x0
    csrrs x14, 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb07, x3
    li x3, 0x15
    csrrs x14, 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb07, x3
    li x3, 0xa
    csrrs x14, 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #MHPMCOUNTER7 Write clear/set value 0x13
    li x3, 0xffffffec
    csrrc x14, 0xb07, x3
    li x3, 0x13
    csrrs x14, 0xb07, x3

    #MHPMCOUNTER7 read value
    csrr x14, 0xb07

    #INSTRET WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTER25 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hd} 
    ##########################
    #MHPMCOUNTER25 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb19, x3
    li x3, 0x1f
    csrrs x14, 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb19, x3
    li x3, 0x0
    csrrs x14, 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb19, x3
    li x3, 0x15
    csrrs x14, 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb19, x3
    li x3, 0xa
    csrrs x14, 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    #MHPMCOUNTER25 Write clear/set value 0xd
    li x3, 0xfffffff2
    csrrc x14, 0xb19, x3
    li x3, 0xd
    csrrs x14, 0xb19, x3

    #MHPMCOUNTER25 read value
    csrr x14, 0xb19

    ##########################
    #PMPADDR11 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'ha} 
    ##########################
    #PMPADDR11 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3bb, x3
    li x3, 0x1f
    csrrs x14, 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3bb, x3
    li x3, 0x0
    csrrs x14, 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3bb, x3
    li x3, 0x15
    csrrs x14, 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3bb, x3
    li x3, 0xa
    csrrs x14, 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    #PMPADDR11 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3bb, x3
    li x3, 0xa
    csrrs x14, 0x3bb, x3

    #PMPADDR11 read value
    csrr x14, 0x3bb

    ##########################
    #MHPMCOUNTERH15 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4} 
    ##########################
    #MHPMCOUNTERH15 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb8f, x3
    li x3, 0x1f
    csrrs x14, 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb8f, x3
    li x3, 0x0
    csrrs x14, 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb8f, x3
    li x3, 0x15
    csrrs x14, 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb8f, x3
    li x3, 0xa
    csrrs x14, 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    #MHPMCOUNTERH15 Write clear/set value 0x4
    li x3, 0xfffffffb
    csrrc x14, 0xb8f, x3
    li x3, 0x4
    csrrs x14, 0xb8f, x3

    #MHPMCOUNTERH15 read value
    csrr x14, 0xb8f

    ##########################
    #MHPMCOUNTER20 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hf} 
    ##########################
    #MHPMCOUNTER20 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb14, x3
    li x3, 0x1f
    csrrs x14, 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb14, x3
    li x3, 0x0
    csrrs x14, 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb14, x3
    li x3, 0x15
    csrrs x14, 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb14, x3
    li x3, 0xa
    csrrs x14, 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    #MHPMCOUNTER20 Write clear/set value 0xf
    li x3, 0xfffffff0
    csrrc x14, 0xb14, x3
    li x3, 0xf
    csrrs x14, 0xb14, x3

    #MHPMCOUNTER20 read value
    csrr x14, 0xb14

    ##########################
    #MHPMEVENT15 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h8} 
    ##########################
    #MHPMEVENT15 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x32f, x3
    li x3, 0x1f
    csrrs x14, 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x32f, x3
    li x3, 0x0
    csrrs x14, 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x32f, x3
    li x3, 0x15
    csrrs x14, 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x32f, x3
    li x3, 0xa
    csrrs x14, 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    #MHPMEVENT15 Write clear/set value 0x8
    li x3, 0xfffffff7
    csrrc x14, 0x32f, x3
    li x3, 0x8
    csrrs x14, 0x32f, x3

    #MHPMEVENT15 read value
    csrr x14, 0x32f

    ##########################
    #MHPMEVENT10 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'ha} 
    ##########################
    #MHPMEVENT10 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x32a, x3
    li x3, 0x1f
    csrrs x14, 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x32a, x3
    li x3, 0x0
    csrrs x14, 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x32a, x3
    li x3, 0x15
    csrrs x14, 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x32a, x3
    li x3, 0xa
    csrrs x14, 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    #MHPMEVENT10 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x32a, x3
    li x3, 0xa
    csrrs x14, 0x32a, x3

    #MHPMEVENT10 read value
    csrr x14, 0x32a

    ##########################
    #MHPMEVENT5 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h3} 
    ##########################
    #MHPMEVENT5 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x325, x3
    li x3, 0x1f
    csrrs x14, 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x325, x3
    li x3, 0x0
    csrrs x14, 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x325, x3
    li x3, 0x15
    csrrs x14, 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x325, x3
    li x3, 0xa
    csrrs x14, 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    #MHPMEVENT5 Write clear/set value 0x3
    li x3, 0xfffffffc
    csrrc x14, 0x325, x3
    li x3, 0x3
    csrrs x14, 0x325, x3

    #MHPMEVENT5 read value
    csrr x14, 0x325

    ##########################
    #MHPMCOUNTER5 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #MHPMCOUNTER5 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb05, x3
    li x3, 0x1f
    csrrs x14, 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb05, x3
    li x3, 0x0
    csrrs x14, 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb05, x3
    li x3, 0x15
    csrrs x14, 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb05, x3
    li x3, 0xa
    csrrs x14, 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    #MHPMCOUNTER5 Write clear/set value 0x1
    li x3, 0xfffffffe
    csrrc x14, 0xb05, x3
    li x3, 0x1
    csrrs x14, 0xb05, x3

    #MHPMCOUNTER5 read value
    csrr x14, 0xb05

    ##########################
    #MHPMCOUNTER22 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h9} 
    ##########################
    #MHPMCOUNTER22 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb16, x3
    li x3, 0x1f
    csrrs x14, 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb16, x3
    li x3, 0x0
    csrrs x14, 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb16, x3
    li x3, 0x15
    csrrs x14, 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb16, x3
    li x3, 0xa
    csrrs x14, 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    #MHPMCOUNTER22 Write clear/set value 0x9
    li x3, 0xfffffff6
    csrrc x14, 0xb16, x3
    li x3, 0x9
    csrrs x14, 0xb16, x3

    #MHPMCOUNTER22 read value
    csrr x14, 0xb16

    ##########################
    #MHPMCOUNTERH28 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h12} 
    ##########################
    #MHPMCOUNTERH28 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb9c, x3
    li x3, 0x1f
    csrrs x14, 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb9c, x3
    li x3, 0x0
    csrrs x14, 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb9c, x3
    li x3, 0x15
    csrrs x14, 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb9c, x3
    li x3, 0xa
    csrrs x14, 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    #MHPMCOUNTERH28 Write clear/set value 0x12
    li x3, 0xffffffed
    csrrc x14, 0xb9c, x3
    li x3, 0x12
    csrrs x14, 0xb9c, x3

    #MHPMCOUNTERH28 read value
    csrr x14, 0xb9c

    ##########################
    #MHPMCOUNTER29 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h16} 
    ##########################
    #MHPMCOUNTER29 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb1d, x3
    li x3, 0x1f
    csrrs x14, 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb1d, x3
    li x3, 0x0
    csrrs x14, 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb1d, x3
    li x3, 0x15
    csrrs x14, 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb1d, x3
    li x3, 0xa
    csrrs x14, 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    #MHPMCOUNTER29 Write clear/set value 0x16
    li x3, 0xffffffe9
    csrrc x14, 0xb1d, x3
    li x3, 0x16
    csrrs x14, 0xb1d, x3

    #MHPMCOUNTER29 read value
    csrr x14, 0xb1d

    ##########################
    #MHPMCOUNTERH29 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1c} 
    ##########################
    #MHPMCOUNTERH29 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb9d, x3
    li x3, 0x1f
    csrrs x14, 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb9d, x3
    li x3, 0x0
    csrrs x14, 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb9d, x3
    li x3, 0x15
    csrrs x14, 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb9d, x3
    li x3, 0xa
    csrrs x14, 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #MHPMCOUNTERH29 Write clear/set value 0x1c
    li x3, 0xffffffe3
    csrrc x14, 0xb9d, x3
    li x3, 0x1c
    csrrs x14, 0xb9d, x3

    #MHPMCOUNTERH29 read value
    csrr x14, 0xb9d

    #CYCLE WR skipped since it's a RO register

    ##########################
    #MHPMEVENT4 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1a} 
    ##########################
    #MHPMEVENT4 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x324, x3
    li x3, 0x1f
    csrrs x14, 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x324, x3
    li x3, 0x0
    csrrs x14, 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x324, x3
    li x3, 0x15
    csrrs x14, 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x324, x3
    li x3, 0xa
    csrrs x14, 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    #MHPMEVENT4 Write clear/set value 0x1a
    li x3, 0xffffffe5
    csrrc x14, 0x324, x3
    li x3, 0x1a
    csrrs x14, 0x324, x3

    #MHPMEVENT4 read value
    csrr x14, 0x324

    ##########################
    #MHPMCOUNTERH4 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hc} 
    ##########################
    #MHPMCOUNTERH4 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb84, x3
    li x3, 0x1f
    csrrs x14, 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb84, x3
    li x3, 0x0
    csrrs x14, 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb84, x3
    li x3, 0x15
    csrrs x14, 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb84, x3
    li x3, 0xa
    csrrs x14, 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    #MHPMCOUNTERH4 Write clear/set value 0xc
    li x3, 0xfffffff3
    csrrc x14, 0xb84, x3
    li x3, 0xc
    csrrs x14, 0xb84, x3

    #MHPMCOUNTERH4 read value
    csrr x14, 0xb84

    ##########################
    #PMPADDR5 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1b} 
    ##########################
    #PMPADDR5 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b5, x3
    li x3, 0x1f
    csrrs x14, 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b5, x3
    li x3, 0x0
    csrrs x14, 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b5, x3
    li x3, 0x15
    csrrs x14, 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b5, x3
    li x3, 0xa
    csrrs x14, 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    #PMPADDR5 Write clear/set value 0x1b
    li x3, 0xffffffe4
    csrrc x14, 0x3b5, x3
    li x3, 0x1b
    csrrs x14, 0x3b5, x3

    #PMPADDR5 read value
    csrr x14, 0x3b5

    ##########################
    #MHPMCOUNTER6 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h14} 
    ##########################
    #MHPMCOUNTER6 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb06, x3
    li x3, 0x1f
    csrrs x14, 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb06, x3
    li x3, 0x0
    csrrs x14, 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb06, x3
    li x3, 0x15
    csrrs x14, 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb06, x3
    li x3, 0xa
    csrrs x14, 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    #MHPMCOUNTER6 Write clear/set value 0x14
    li x3, 0xffffffeb
    csrrc x14, 0xb06, x3
    li x3, 0x14
    csrrs x14, 0xb06, x3

    #MHPMCOUNTER6 read value
    csrr x14, 0xb06

    ##########################
    #MHPMCOUNTERH23 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #MHPMCOUNTERH23 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb97, x3
    li x3, 0x1f
    csrrs x14, 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb97, x3
    li x3, 0x0
    csrrs x14, 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb97, x3
    li x3, 0x15
    csrrs x14, 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb97, x3
    li x3, 0xa
    csrrs x14, 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    #MHPMCOUNTERH23 Write clear/set value 0x18
    li x3, 0xffffffe7
    csrrc x14, 0xb97, x3
    li x3, 0x18
    csrrs x14, 0xb97, x3

    #MHPMCOUNTERH23 read value
    csrr x14, 0xb97

    ##########################
    #PMPADDR6 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1} 
    ##########################
    #PMPADDR6 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b6, x3
    li x3, 0x1f
    csrrs x14, 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b6, x3
    li x3, 0x0
    csrrs x14, 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b6, x3
    li x3, 0x15
    csrrs x14, 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b6, x3
    li x3, 0xa
    csrrs x14, 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    #PMPADDR6 Write clear/set value 0x1
    li x3, 0xfffffffe
    csrrc x14, 0x3b6, x3
    li x3, 0x1
    csrrs x14, 0x3b6, x3

    #PMPADDR6 read value
    csrr x14, 0x3b6

    ##########################
    #MHPMCOUNTER19 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'hb} 
    ##########################
    #MHPMCOUNTER19 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb13, x3
    li x3, 0x1f
    csrrs x14, 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb13, x3
    li x3, 0x0
    csrrs x14, 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb13, x3
    li x3, 0x15
    csrrs x14, 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb13, x3
    li x3, 0xa
    csrrs x14, 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    #MHPMCOUNTER19 Write clear/set value 0xb
    li x3, 0xfffffff4
    csrrc x14, 0xb13, x3
    li x3, 0xb
    csrrs x14, 0xb13, x3

    #MHPMCOUNTER19 read value
    csrr x14, 0xb13

    ##########################
    #MHPMCOUNTERH8 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h8} 
    ##########################
    #MHPMCOUNTERH8 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb88, x3
    li x3, 0x1f
    csrrs x14, 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb88, x3
    li x3, 0x0
    csrrs x14, 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb88, x3
    li x3, 0x15
    csrrs x14, 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb88, x3
    li x3, 0xa
    csrrs x14, 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    #MHPMCOUNTERH8 Write clear/set value 0x8
    li x3, 0xfffffff7
    csrrc x14, 0xb88, x3
    li x3, 0x8
    csrrs x14, 0xb88, x3

    #MHPMCOUNTERH8 read value
    csrr x14, 0xb88

    ##########################
    #PMPADDR8 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h2} 
    ##########################
    #PMPADDR8 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x3b8, x3
    li x3, 0x1f
    csrrs x14, 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x3b8, x3
    li x3, 0x0
    csrrs x14, 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x3b8, x3
    li x3, 0x15
    csrrs x14, 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x3b8, x3
    li x3, 0xa
    csrrs x14, 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #PMPADDR8 Write clear/set value 0x2
    li x3, 0xfffffffd
    csrrc x14, 0x3b8, x3
    li x3, 0x2
    csrrs x14, 0x3b8, x3

    #PMPADDR8 read value
    csrr x14, 0x3b8

    #MIMPID WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTERH6 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h6} 
    ##########################
    #MHPMCOUNTERH6 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb86, x3
    li x3, 0x1f
    csrrs x14, 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb86, x3
    li x3, 0x0
    csrrs x14, 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb86, x3
    li x3, 0x15
    csrrs x14, 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb86, x3
    li x3, 0xa
    csrrs x14, 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    #MHPMCOUNTERH6 Write clear/set value 0x6
    li x3, 0xfffffff9
    csrrc x14, 0xb86, x3
    li x3, 0x6
    csrrs x14, 0xb86, x3

    #MHPMCOUNTERH6 read value
    csrr x14, 0xb86

    ##########################
    #MHPMCOUNTER4 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h18} 
    ##########################
    #MHPMCOUNTER4 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb04, x3
    li x3, 0x1f
    csrrs x14, 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb04, x3
    li x3, 0x0
    csrrs x14, 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb04, x3
    li x3, 0x15
    csrrs x14, 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb04, x3
    li x3, 0xa
    csrrs x14, 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    #MHPMCOUNTER4 Write clear/set value 0x18
    li x3, 0xffffffe7
    csrrc x14, 0xb04, x3
    li x3, 0x18
    csrrs x14, 0xb04, x3

    #MHPMCOUNTER4 read value
    csrr x14, 0xb04

    ##########################
    #MHPMCOUNTERH3 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h11} 
    ##########################
    #MHPMCOUNTERH3 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb83, x3
    li x3, 0x1f
    csrrs x14, 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb83, x3
    li x3, 0x0
    csrrs x14, 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb83, x3
    li x3, 0x15
    csrrs x14, 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb83, x3
    li x3, 0xa
    csrrs x14, 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    #MHPMCOUNTERH3 Write clear/set value 0x11
    li x3, 0xffffffee
    csrrc x14, 0xb83, x3
    li x3, 0x11
    csrrs x14, 0xb83, x3

    #MHPMCOUNTERH3 read value
    csrr x14, 0xb83

    ##########################
    #MHPMCOUNTERH25 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1f} 
    ##########################
    #MHPMCOUNTERH25 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb99, x3
    li x3, 0x1f
    csrrs x14, 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb99, x3
    li x3, 0x0
    csrrs x14, 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb99, x3
    li x3, 0x15
    csrrs x14, 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb99, x3
    li x3, 0xa
    csrrs x14, 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    #MHPMCOUNTERH25 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb99, x3
    li x3, 0x1f
    csrrs x14, 0xb99, x3

    #MHPMCOUNTERH25 read value
    csrr x14, 0xb99

    ##########################
    #MHPMCOUNTERH11 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1e} 
    ##########################
    #MHPMCOUNTERH11 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb8b, x3
    li x3, 0x1f
    csrrs x14, 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb8b, x3
    li x3, 0x0
    csrrs x14, 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb8b, x3
    li x3, 0x15
    csrrs x14, 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb8b, x3
    li x3, 0xa
    csrrs x14, 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHPMCOUNTERH11 Write clear/set value 0x1e
    li x3, 0xffffffe1
    csrrc x14, 0xb8b, x3
    li x3, 0x1e
    csrrs x14, 0xb8b, x3

    #MHPMCOUNTERH11 read value
    csrr x14, 0xb8b

    #MHARTID WR skipped since it's a RO register

    ##########################
    #MHPMCOUNTER27 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h19} 
    ##########################
    #MHPMCOUNTER27 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb1b, x3
    li x3, 0x1f
    csrrs x14, 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb1b, x3
    li x3, 0x0
    csrrs x14, 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb1b, x3
    li x3, 0x15
    csrrs x14, 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb1b, x3
    li x3, 0xa
    csrrs x14, 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    #MHPMCOUNTER27 Write clear/set value 0x19
    li x3, 0xffffffe6
    csrrc x14, 0xb1b, x3
    li x3, 0x19
    csrrs x14, 0xb1b, x3

    #MHPMCOUNTER27 read value
    csrr x14, 0xb1b

    ##########################
    #MHPMEVENT17 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h13} 
    ##########################
    #MHPMEVENT17 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x331, x3
    li x3, 0x1f
    csrrs x14, 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x331, x3
    li x3, 0x0
    csrrs x14, 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x331, x3
    li x3, 0x15
    csrrs x14, 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x331, x3
    li x3, 0xa
    csrrs x14, 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    #MHPMEVENT17 Write clear/set value 0x13
    li x3, 0xffffffec
    csrrc x14, 0x331, x3
    li x3, 0x13
    csrrs x14, 0x331, x3

    #MHPMEVENT17 read value
    csrr x14, 0x331

    ##########################
    #MEPC testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h7} 
    ##########################
    #MEPC Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x341, x3
    li x3, 0x1f
    csrrs x14, 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x341, x3
    li x3, 0x0
    csrrs x14, 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x341, x3
    li x3, 0x15
    csrrs x14, 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x341, x3
    li x3, 0xa
    csrrs x14, 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    #MEPC Write clear/set value 0x7
    li x3, 0xfffffff8
    csrrc x14, 0x341, x3
    li x3, 0x7
    csrrs x14, 0x341, x3

    #MEPC read value
    csrr x14, 0x341

    ##########################
    #MINSTRET testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1d} 
    ##########################
    #MINSTRET Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0xb02, x3
    li x3, 0x1f
    csrrs x14, 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0xb02, x3
    li x3, 0x0
    csrrs x14, 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0xb02, x3
    li x3, 0x15
    csrrs x14, 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0xb02, x3
    li x3, 0xa
    csrrs x14, 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    #MINSTRET Write clear/set value 0x1d
    li x3, 0xffffffe2
    csrrc x14, 0xb02, x3
    li x3, 0x1d
    csrrs x14, 0xb02, x3

    #MINSTRET read value
    csrr x14, 0xb02

    ##########################
    #MHPMEVENT29 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h1b} 
    ##########################
    #MHPMEVENT29 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x33d, x3
    li x3, 0x1f
    csrrs x14, 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x33d, x3
    li x3, 0x0
    csrrs x14, 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x33d, x3
    li x3, 0x15
    csrrs x14, 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x33d, x3
    li x3, 0xa
    csrrs x14, 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    #MHPMEVENT29 Write clear/set value 0x1b
    li x3, 0xffffffe4
    csrrc x14, 0x33d, x3
    li x3, 0x1b
    csrrs x14, 0x33d, x3

    #MHPMEVENT29 read value
    csrr x14, 0x33d

    ##########################
    #MHPMEVENT20 testing W/R values '{'h1f, 'h0, 'h15, 'ha, 'h4} 
    ##########################
    #MHPMEVENT20 Write clear/set value 0x1f
    li x3, 0xffffffe0
    csrrc x14, 0x334, x3
    li x3, 0x1f
    csrrs x14, 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write clear/set value 0x0
    li x3, 0xffffffff
    csrrc x14, 0x334, x3
    li x3, 0x0
    csrrs x14, 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write clear/set value 0x15
    li x3, 0xffffffea
    csrrc x14, 0x334, x3
    li x3, 0x15
    csrrs x14, 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write clear/set value 0xa
    li x3, 0xfffffff5
    csrrc x14, 0x334, x3
    li x3, 0xa
    csrrs x14, 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    #MHPMEVENT20 Write clear/set value 0x4
    li x3, 0xfffffffb
    csrrc x14, 0x334, x3
    li x3, 0x4
    csrrs x14, 0x334, x3

    #MHPMEVENT20 read value
    csrr x14, 0x334

    ret
