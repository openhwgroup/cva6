.text
    nop
    nop
    nop
    addi x1, x0, 1
    addi x2, x0, 1
    add  x3, x1, x2
    add  x3, x1, x2
    add  x4, x2, x3
    add  x5, x3, x4
    add  x6, x4, x5
    add  x7, x5, x6
    add  x8, x6, x7
    csrw mstatus, x7
    add  x9, x7, x8
    csrr x1, mstatus
    nop
L0: jal L1
    nop
    nop
    nop
    nop
    nop
    nop
L1: jal L0
    nop
    nop
    addi x1, x0, 55