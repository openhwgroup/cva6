# ------------------------------------------------------------------------------
#   Copyright 2026 Thales France
#
#   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#   You may obtain a copy of the License at https://solderpad.org/licenses/
# ------------------------------------------------------------------------------
#   sdtrig_napot_guard_test.S
#
#   Pins the NAPOT guard of the trigger module.
#
#   The Sdtrig spec encodes a naturally aligned power-of-two range in tdata2 as
#   the base address followed by a run of low ones: a 32-byte range based at
#   0x80003000 is written 0x8000300f. The module guards the comparison with
#
#       is_valid_napot = ((base & (base + 1)) == 0)
#
#   which requires base + 1 to be a power of two across the whole register, so
#   base has to be 0b0..01..1. Only a range based at address zero passes, and a
#   NAPOT pattern built on a real code address is rejected outright.
#
#   This test does not assert which behaviour is correct. It records the one the
#   RTL has: a spec-shaped NAPOT pattern over an executed instruction does not
#   fire. Should the guard be relaxed to look at the low bits only, this test
#   turns red and the change gets noticed instead of passing silently.
#
#   Requires Sdtrig, SdtrigMcontrol6, SdtrigMcontrol6ExecAddr, and bit 1 of
#   SdtrigSupportedMatch.
# ------------------------------------------------------------------------------

    .text
    # The handler steps over the trapping instruction with mepc + 4, so every
    # instruction it can land on has to be four bytes wide.
    .option norvc

    .globl main
main:
    la   t0, trap_handler
    csrw mtvec, t0
    la   t0, fire_count
    sw   zero, 0(t0)

    # --------------------------------------------------------------------
    # Arm a NAPOT trigger the way the spec says, over the address of the
    # instruction below: base address with the low four bits set, which is a
    # 32-byte range containing it.
    # --------------------------------------------------------------------
    li   t0, 0
    csrw 0x7a0, t0              # tselect = 0

    la   t1, napot_target
    andi t1, t1, -32            # align down to the 32-byte boundary
    ori  t1, t1, 0x0f           # trailing ones: 32-byte NAPOT range
    csrw 0x7a2, t1

    # type 6, match 1 (NAPOT) in [10:7], m in [6], execute in [2]
    li   t1, 0x600000c4
    csrw 0x7a1, t1

napot_target:
    nop                         # inside the range the spec describes

    # --------------------------------------------------------------------
    # Current behaviour: the guard rejects the pattern, so nothing fired.
    # --------------------------------------------------------------------
    la   t0, fire_count
    lw   t1, 0(t0)
    bnez t1, unexpected_fire

    # Disarm before leaving.
    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero

    # --------------------------------------------------------------------
    # The same trigger with a pattern the guard does accept, 0x0000000f, a
    # 16-byte range based at zero. No code lives there, so this still must not
    # fire; what it checks is that a guard-accepted pattern does not match an
    # address outside its range, which is the comparison itself working.
    # --------------------------------------------------------------------
    la   t0, fire_count
    sw   zero, 0(t0)

    li   t0, 0
    csrw 0x7a0, t0
    li   t1, 0x0000000f         # valid NAPOT, range 0x0..0xf
    csrw 0x7a2, t1
    li   t1, 0x600000c4
    csrw 0x7a1, t1

    nop                         # at 0x8000xxxx, well outside 0x0..0xf
    nop

    la   t0, fire_count
    lw   t1, 0(t0)
    bnez t1, unexpected_fire

    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero

    # --------------------------------------------------------------------
    li a0, 0
    ret

unexpected_fire:
    # Reaching here means a NAPOT trigger fired where it currently cannot.
    # Disarm first, otherwise the trigger keeps firing on the way out.
    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero
    li a0, 1
    ret

    # --------------------------------------------------------------------
    # Counts breakpoint traps and steps over the instruction that trapped.
    # --------------------------------------------------------------------
    .align 6
trap_handler:
    addi sp, sp, -16
    sw   t0, 0(sp)
    sw   t1, 4(sp)

    csrr t0, mcause
    li   t1, 3                  # breakpoint
    bne  t0, t1, handler_out

    la   t0, fire_count
    lw   t1, 0(t0)
    addi t1, t1, 1
    sw   t1, 0(t0)

    csrr t0, mepc
    addi t0, t0, 4
    csrw mepc, t0

handler_out:
    lw   t0, 0(sp)
    lw   t1, 4(sp)
    addi sp, sp, 16
    mret

    .data
    .align 2
fire_count:
    .word 0
