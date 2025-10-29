.text
.globl _start
_start:
    # Mcontrol6 trigger only supports action = 1 i.e. enter debug mode
    li x2, 0
    csrw tselect, x2

    li x5, 0x80003000 ## test address for matching
    li x6, 0x12345678 ## test data for matching

    li x3, 0x12345678  # match value loaded here
    csrw tdata2, x3

    ## Trigger Configuration
    ## Test 1): store with data match
    li x4, 0x60201042
    csrw tdata1, x4
    nop
    nop
    nop
    nop
    sw x6, 0(x5)
    
    ##Test 2): load with data match
    # li x4, 0x60201041
    # csrw tdata1, x4
    # nop
    # nop
    # nop
    # nop
    # nop
    # lw x7, 0(x5)

    ## Test 3): store with address match
    # li x4, 0x60001042
    # csrw tdata1, x4
    # sw x6, 4(x5)
    # nop
    # nop
    # nop

    ## Test 4): load with address match
    # li x4, 0x60001041
    # csrw tdata1, x4
    # lw x7, 4(x5)
    # nop
    # nop
    # nop

    ## Test 5): execute with instruction match
    # li x4, 0x60201044
    # csrw tdata1, x4
    # add x8, x2, x3
    # nop
    # nop

    # # Test 6): execute with address match
    # li x4, 0x60001044
    # csrw tdata1, x4
    # csrr x7, tdata1
    # nop
    # nop
    # nop
    # nop
    # nop
    # nop

    nop
    nop
    nop
    nop
    nop
    
exit:
    li x1, 1
    la t0, tohost
    sw x1, 0(t0)
    j exit

.data
.align 4
.global tohost
tohost: .word 0
.global fromhost
fromhost: .word 0