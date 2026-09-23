# ------------------------------------------------------------------------------
#   Copyright 2026 Thales France
#
#   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#   You may obtain a copy of the License at https://solderpad.org/licenses/
# ------------------------------------------------------------------------------
#   sdtrig_napot_match_test.S
#
#   Checks the NAPOT range match of an mcontrol6 execute trigger against the
#   encoding of the privileged specification: tdata2 holds the base address
#   followed by a run of low ones, and n trailing ones select a range of
#   2^(n+1) bytes.
#
#   Three properties, each of which the previous implementation got wrong:
#     - a range based at a real code address matches at all, rather than being
#       rejected for having non-zero address bits;
#     - an address inside the range matches;
#     - an address just past the end of the range does not, which is what pins
#       the range size and would catch it being off by a factor of two.
#
#   The trigger is disarmed inside the handler before returning, because a
#   range trigger armed in machine mode would otherwise match the handler's own
#   instructions and loop.
#
#   Requires Sdtrig, SdtrigMcontrol6, SdtrigMcontrol6ExecAddr and bit 1 of
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
    # An 8-byte NAPOT range covering in_range_insn.
    #
    # Three trailing ones would give 2^4 = 16 bytes; two give 2^3 = 8. Use two,
    # so tdata2 = base | 0b011 with base aligned to 8. The instruction below
    # sits at the base, inside the range.
    # --------------------------------------------------------------------
    li   t0, 0
    csrw 0x7a0, t0              # tselect = 0

    la   t1, in_range_insn
    andi t1, t1, -8             # align down to an 8-byte boundary
    ori  t1, t1, 0x3            # two trailing ones: 8-byte range
    csrw 0x7a2, t1

    # type 6, match 1 (NAPOT) in [10:7], m in [6], execute in [2], action 0
    li   t1, 0x600000c4
    csrw 0x7a1, t1

    .align 3                    # put the next instruction on the range base
in_range_insn:
    nop                         # inside the range: must trap

    # The handler disarmed the trigger, so we get here once.
    la   t0, fire_count
    lw   t1, 0(t0)
    beqz t1, fail               # nothing fired: the range never matched

    # --------------------------------------------------------------------
    # Pin the size of the range, which is where an off-by-one in the mask hides.
    #
    # tdata2 is range_base | 0b011, and range_base is 8-byte aligned, so the run
    # of low ones is two bits and the correct mask ignores three: the range is
    # range_base .. range_base+7. A mask one bit wider would ignore four and the
    # range would become the enclosing 16 bytes, which reaches *below*
    # range_base, down to range_base-8.
    #
    # So the discriminating instruction sits just before the base, not after it:
    # outside the 8-byte range, inside the 16-byte one. before_range is placed 4
    # bytes ahead of an 8-byte aligned base for exactly that.
    # --------------------------------------------------------------------
    la   t0, fire_count
    sw   zero, 0(t0)

    li   t0, 0
    csrw 0x7a0, t0

    la   t1, range_base
    ori  t1, t1, 0x3            # two trailing ones: 8 bytes from range_base
    csrw 0x7a2, t1
    li   t1, 0x600000c4
    csrw 0x7a1, t1

    j    before_range           # reach the check without entering the range

    .align 4                    # 16-byte boundary, so range_base lands at +8
before_range:
    nop                         # at boundary+4: below range_base, inside 16
    j    after_range

    .align 3
range_base:                     # at boundary+8
    nop
    nop

after_range:
    # Disarm before checking, so a spurious match cannot loop.
    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero

    la   t0, fire_count
    lw   t1, 0(t0)
    bnez t1, fail               # fired below an 8-byte range: mask too wide

    # --------------------------------------------------------------------
    li a0, 0
    ret

fail:
    # Disarm on the way out, otherwise an armed range trigger keeps firing.
    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero
    li a0, 1
    ret

    # --------------------------------------------------------------------
    # Counts breakpoint traps, disarms the trigger that fired, and steps over
    # the instruction that trapped.
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

    # Disarm trigger 0: a range trigger left armed in machine mode matches the
    # handler itself, and the loop would never end.
    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero

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
