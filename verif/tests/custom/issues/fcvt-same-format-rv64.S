# Copyright 2026
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

.section .text

.globl main
main:
    la t0, trap_count
    sw zero, 0(t0)

    la t0, alt_trap_count
    sw zero, 0(t0)

    # Defined S/D cross-format conversions. These must not trap.

    # fcvt.s.d f2, f0, rne
    .word 0x40100153

    # fcvt.d.s f2, f0, rne
    .word 0x42000153

same_format_begin:

    # Reserved same-format encoding: "fcvt.s.s"
    .word 0x40000153

    # Reserved same-format encoding: "fcvt.d.d"
    .word 0x42100153

same_format_end:

    # Exactly the two reserved S/D encodings above must have trapped.
    la t0, trap_count
    lw t1, 0(t0)
    li t2, 2
    bne t1, t2, failure

    # Probe for a configuration supporting both FP16 and FP16ALT.
    #
    # FP16 -> FP16ALT:
    #   destination fmt = 10
    #   destination ALT selector rm = 101
    #   source = 010
    #
    # If this instruction is illegal, the trap handler skips the optional
    # XF16ALT portion of the test.
xf16alt_probe:
    .word 0x44205153

    # Legal FP16ALT -> FP16 conversion:
    #   destination fmt = 10, rm = 000
    #   source = 110
xf16alt_control_2:
    .word 0x44600153

xf16alt_same_format_begin:

    # Reserved FP16 -> FP16 same-format conversion.
    .word 0x44200153

    # Reserved FP16ALT -> FP16ALT same-format conversion.
    .word 0x44605153

xf16alt_same_format_end:

    # On an FP16+FP16ALT configuration both same-format encodings
    # above must have trapped.
    la t0, alt_trap_count
    lw t1, 0(t0)
    li t2, 2
    bne t1, t2, failure

xf16alt_skip:
    li a0, 0
    ret

failure:
    li a0, 1
    ret


.globl handle_trap
handle_trap:
    # crt.S passes:
    #   a0 = mcause
    #   a1 = mepc

    # Only illegal-instruction exceptions are expected.
    li t0, 2
    bne a0, t0, unexpected_trap

    # First check the S/D same-format instructions.
    la t0, same_format_begin
    bltu a1, t0, check_xf16alt

    la t1, same_format_end
    bgeu a1, t1, check_xf16alt

    sub t2, a1, t0
    andi t3, t2, 3
    bnez t3, unexpected_trap

    srli t2, t2, 2
    li t3, 2
    bgeu t2, t3, unexpected_trap

    la t0, trap_count
    lw t1, 0(t0)

    # Require the expected traps to occur in order.
    bne t1, t2, unexpected_trap

    addi t1, t1, 1
    sw t1, 0(t0)

    # Skip the faulting 32-bit instruction.
    addi a0, a1, 4
    ret


check_xf16alt:
    # If the first legal FP16 -> FP16ALT probe itself traps, this
    # configuration does not support the optional test combination.
    la t0, xf16alt_probe
    beq a1, t0, xf16alt_unavailable

    # The second cross-format control must not trap if the probe passed.
    addi t0, t0, 4
    beq a1, t0, unexpected_trap

    # Check the two expected XF16/ALT same-format traps.
    la t0, xf16alt_same_format_begin
    bltu a1, t0, unexpected_trap

    la t1, xf16alt_same_format_end
    bgeu a1, t1, unexpected_trap

    sub t2, a1, t0
    andi t3, t2, 3
    bnez t3, unexpected_trap

    srli t2, t2, 2
    li t3, 2
    bgeu t2, t3, unexpected_trap

    la t0, alt_trap_count
    lw t1, 0(t0)

    # Require both same-format traps in instruction order.
    bne t1, t2, unexpected_trap

    addi t1, t1, 1
    sw t1, 0(t0)

    addi a0, a1, 4
    ret


xf16alt_unavailable:
    # Skip the optional XF16ALT checks when this configuration
    # does not implement both formats.
    la a0, xf16alt_skip
    ret


unexpected_trap:
    la a0, failure
    ret


.section .data
.align 2

trap_count:
    .word 0

alt_trap_count:
    .word 0
