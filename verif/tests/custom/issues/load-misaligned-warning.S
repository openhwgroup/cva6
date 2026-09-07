.section .text

.globl main
main:
    la      t0, data_buf

    # Word load at byte offset 5.
    # This is architecturally misaligned and also triggers addr_offset0.
    addi    t1, t0, 5
    lw      t2, 0(t1)

    # Unsigned word load at the same offset.
    addi    t1, t0, 5
    lwu     t2, 0(t1)

    # Halfword load at byte offset 7.
    # This is architecturally misaligned and also triggers addr_offset1.
    addi    t1, t0, 7
    lh      t2, 0(t1)

    # Unsigned halfword load at the same offset.
    addi    t1, t0, 7
    lhu     t2, 0(t1)

    # All four loads must have trapped.
    la      t0, trap_count
    lw      t1, 0(t0)
    li      t2, 4
    bne     t1, t2, fail

    li      a0, 0
    ret

fail:
    li      a0, 1
    ret


.globl handle_trap
handle_trap:
    # crt.S passes:
    #   a0 = mcause
    #   a1 = mepc
    # and expects the return value in a0 to be the resume PC.

    li      t0, 4
    bne     a0, t0, unexpected_trap

    la      t0, trap_count
    lw      t1, 0(t0)
    addi    t1, t1, 1
    sw      t1, 0(t0)

    # All faulting loads in this test are 32-bit instructions.
    addi    a0, a1, 4
    ret

unexpected_trap:
    li      a0, 2
    j       _exit


.section .data
.align 3

data_buf:
    .dword  0x1122334455667788
    .dword  0x99aabbccddeeff00

.align 2
trap_count:
    .word   0
