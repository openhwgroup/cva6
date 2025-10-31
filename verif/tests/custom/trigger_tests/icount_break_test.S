.text
.globl _start
_start:
    # Ensure DebugEn is disabled when using action 0 i.e. breakpoint action
    la t0, trap_handler
    csrw mtvec, t0

    li t1, 0x8
    csrs mstatus, t1

    li x2, 0
    csrw tselect, x2


    li x2, 0x30003e00    # count 15 instructions and go into breakpoint exception
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

trap_handler:
    csrr t3, mcause
    csrr t4, mepc

    addi t4, t4, 4
    csrw mepc, t4

    mret

.data
.align 4
.global tohost
tohost: .word 0
.global fromhost
fromhost: .word 0
