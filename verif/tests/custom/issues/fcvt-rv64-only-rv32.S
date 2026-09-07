# Copyright 2026
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

.section .text

.globl main
main:
    la t0, trap_count
    sw zero, 0(t0)

    # Legal RV32 F conversions. These must not trap.
    #
    # fcvt.w.s x0, f0
    .word 0xc0000053

    # fcvt.wu.s x0, f0
    .word 0xc0100053

    # fcvt.s.w f0, x0
    .word 0xd0000053

    # fcvt.s.wu f0, x0
    .word 0xd0100053

    # RV64-only conversions. Each must raise an
    # illegal-instruction exception when XLEN=32.
    #
rv64_only_begin:
    # fcvt.l.s x0, f0
    .word 0xc0200053

    # fcvt.lu.s x0, f0
    .word 0xc0300053

    # fcvt.s.l f0, x0
    .word 0xd0200053

    # fcvt.s.lu f0, x0
    .word 0xd0300053

    # Exactly the four RV64-only instructions above
    # must have trapped.
    la t0, trap_count
    lw t1, 0(t0)
    li t2, 4
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
    #
    # Only illegal-instruction exceptions are expected.
    li t0, 2
    bne a0, t0, unexpected_trap

    la t0, trap_count
    lw t1, 0(t0)

    # Reject extra traps and traps from any other instruction.
    li t2, 4
    bgeu t1, t2, unexpected_trap

    # The four expected instructions occupy consecutive 4-byte slots.
    la t2, rv64_only_begin
    slli t3, t1, 2
    add t2, t2, t3
    bne a1, t2, unexpected_trap

    addi t1, t1, 1
    sw t1, 0(t0)

    # Skip the injected 32-bit instruction.
    addi a0, a1, 4
    ret

unexpected_trap:
    # Resume at the failure path.
    la a0, failure
    ret


.section .data
.align 2

trap_count:
    .word 0
