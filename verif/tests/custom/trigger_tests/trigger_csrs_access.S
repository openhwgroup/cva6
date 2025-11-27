.text
.globl _start
_start:
    ## TM CSRs read write test. Since the fields are WARL, written data may not match read data.
    # Check CSR TSELECT
    li x2, 2
    csrw tselect, x2

    # Check CSR TDATA2
    li x4, 0x00000008
    csrw tdata2, x4

    # Check CSR TDATA1
    li x5, 0x50000201
    csrw tdata1, x5

    # Check CSR TDATA3
    li x8, 0x50021090
    csrw tdata3, x8

    csrr x3, tselect
    csrr x6, tdata2
    csrr x7, tdata1
    csrr x9, tdata3

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
