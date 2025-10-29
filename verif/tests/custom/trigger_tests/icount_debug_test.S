.text
.globl _start
_start:
    li x2, 0
    csrw tselect, x2


    li x2, 0x30003e01    # count 15 instructions and enter debug mode
    nop
    nop
    nop
    csrw tdata1, x2

    # dummy instructions to count
    csrr x7, tdata1
    csrr x7, tdata1
    csrr x7, tdata1
    csrr x7, tdata1
    li x3, 1
    nop
    nop
    nop
    li x4, 2
    nop
    nop
    nop
    li x5, 3
    nop
    nop
    nop
    li x2, 0
    nop
    li x2, 1
    li x2, 2

exit:
    li a1, 1
    la t2, tohost
    sw a1, 0(t2)
    j exit

.data
.align 4
.global tohost
tohost: .word 0
.global fromhost
fromhost: .word 0
