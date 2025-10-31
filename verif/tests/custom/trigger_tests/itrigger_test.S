.section .text
.globl _start
_start:
    # For emulating a software interrupt
    la t0, trap_handler
    csrw mtvec, t0

    li t1, 0x8
    csrs mie, t1
    csrs mstatus, t1

    # Trigger setup
    li x2, 1
    csrw tselect, x2

    li x3, 0x00000008  # match on software interrupt
    csrw tdata2, x3

    li x4, 0x40000201  # match on software interrupt and enter debug mode
    csrw tdata1, x4
    csrr x5, tdata1

    # For emulating a software interrupt
    li t2, 0x02000000   # msip (clint) base address
    li t3, 1
    sw t3, 0(t2)
    fence
    wfi
    nop
    nop
    nop
    nop
    nop
    nop

exit:
    li a1, 1
    la t2, tohost
    sw a1, 0(t2)
    j exit

trap_handler:
    # For emulating a software interrupt
    csrr a0, mcause
    csrr a1, mepc

    li t0, 0x02000000
    sw zero, 0(t0)   # clear MSIP (for software interrupt)
    fence

    mret

.data
.align 4
.global tohost
tohost: .word 0
.global fromhost
fromhost: .word 0
