# Copyright 2026
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

.section .text

.globl main
main:
    la t0, trap_count
    sw zero, 0(t0)

    # Defined cross-format conversions. These must not trap.

    # fcvt.s.d f2, f0, rne
    .word 0x40100153

    # fcvt.d.s f2, f0, rne
    .word 0x42000153

same_format_begin:

    # Reserved same-format encoding: "fcvt.s.s"
    .word 0x40000153

    # Reserved same-format encoding: "fcvt.d.d"
    .word 0x42100153

    # Exactly the two reserved encodings above must have trapped.
    la t0, trap_count
    lw t1, 0(t0)
    li t2, 2
    bne t1, t2, failure

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

    la t0, trap_count
    lw t1, 0(t0)

    li t2, 2
    bgeu t1, t2, unexpected_trap

    # Check that mepc identifies the expected raw instruction.
    la t2, same_format_begin
    slli t3, t1, 2
    add t2, t2, t3
    bne a1, t2, unexpected_trap

    addi t1, t1, 1
    sw t1, 0(t0)

    # Skip the faulting 32-bit instruction.
    addi a0, a1, 4
    ret

unexpected_trap:
    la a0, failure
    ret


.section .data
.align 2

trap_count:
    .word 0
