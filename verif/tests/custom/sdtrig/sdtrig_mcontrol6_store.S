# ------------------------------------------------------------------------------
#   Copyright 2026 Thales France
#
#   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#   You may obtain a copy of the License at https://solderpad.org/licenses/
# ------------------------------------------------------------------------------
#   sdtrig_mcontrol6_store.S
#
#   mcontrol6 store triggers, both comparison targets:
#     - select = 0, compare the store address;
#     - select = 1, compare the value being stored.
#
#   A store trigger is precise: it fires before the store reaches memory, so the
#   test checks the memory location is still untouched inside the handler. That
#   is the property worth having, the trigger being useless as a watchpoint if
#   the write has already happened.
#
#   tdata1 layout for mcontrol6 on RV32, as the module decodes it:
#     [31:28] type = 6      [22] hit0     [21] select    [18:16] size
#     [15:12] action        [11] chain    [10:7] match   [6] m
#     [4] s   [3] u   [2] execute   [1] store   [0] load
#
#   Requires Sdtrig, SdtrigMcontrol6 and SdtrigMcontrol6Store.
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
    # Store address match: fire on a store to watched_word, whatever the value.
    # --------------------------------------------------------------------
    la   t0, watched_word
    li   t1, 0
    sw   t1, 0(t0)              # start from a known value, trigger disarmed

    li   t0, 0
    csrw 0x7a0, t0              # tselect = 0
    la   t1, watched_word
    csrw 0x7a2, t1              # tdata2 = the address to watch

    # type 6, match 0 (equal), m, store, action 0 (breakpoint), select = 0
    li   t1, 0x60000042
    csrw 0x7a1, t1

    la   t0, watched_word
    li   t1, 0xA5A5A5A5
    sw   t1, 0(t0)              # must trap before writing

    # The handler disarmed the trigger and stepped over the store, so the value
    # must still be the one we set before arming: the store never happened.
    la   t0, fire_count
    lw   t1, 0(t0)
    li   t2, 1
    bne  t1, t2, fail           # exactly one fire expected

    la   t0, watched_word
    lw   t1, 0(t0)
    bnez t1, fail               # the store went through: not a watchpoint

    # --------------------------------------------------------------------
    # Store data match: fire on the value being stored, at any address.
    # --------------------------------------------------------------------
    la   t0, fire_count
    sw   zero, 0(t0)
    la   t0, other_word
    li   t1, 0
    sw   t1, 0(t0)

    li   t0, 0
    csrw 0x7a0, t0
    li   t1, 0xDEADBEEF
    csrw 0x7a2, t1              # tdata2 = the value to watch for

    # same, with select = 1 in [21] so the comparison is against the data
    li   t1, 0x60200042
    csrw 0x7a1, t1

    la   t0, other_word
    li   t1, 0xDEADBEEF
    sw   t1, 0(t0)              # storing the watched value: must trap

    la   t0, fire_count
    lw   t1, 0(t0)
    li   t2, 1
    bne  t1, t2, fail

    la   t0, other_word
    lw   t1, 0(t0)
    bnez t1, fail               # the store went through

    # --------------------------------------------------------------------
    # A store of a different value must not fire the data trigger. This is what
    # tells a working comparison from one that fires on every store.
    # --------------------------------------------------------------------
    la   t0, fire_count
    sw   zero, 0(t0)

    li   t0, 0
    csrw 0x7a0, t0
    li   t1, 0xDEADBEEF
    csrw 0x7a2, t1
    li   t1, 0x60200042
    csrw 0x7a1, t1

    la   t0, other_word
    li   t1, 0x12345678
    sw   t1, 0(t0)              # a value that does not match

    # Disarm before checking, so a spurious match cannot loop.
    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero

    la   t0, fire_count
    lw   t1, 0(t0)
    bnez t1, fail               # fired on a value it was not watching

    la   t0, other_word
    lw   t1, 0(t0)
    li   t2, 0x12345678
    bne  t1, t2, fail           # this store was supposed to go through

    # --------------------------------------------------------------------
    li a0, 0
    ret

fail:
    # Disarm on the way out, otherwise an armed trigger keeps firing.
    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero
    li a0, 1
    ret

    # --------------------------------------------------------------------
    # Counts breakpoint traps, disarms the trigger, and steps over the store
    # that trapped so the test can carry on.
    # --------------------------------------------------------------------
    .align 6
trap_handler:
    # No stack, and no memory write before the trigger is disarmed. A store data
    # trigger watches every write of the value it holds, and the handler would
    # otherwise fire it again the moment it spilled the register still carrying
    # that value. Disarm first, count second.
    #
    # s10 and s11 are scratch here; main does not use them.
    csrr s10, mcause
    li   s11, 3                 # breakpoint
    bne  s10, s11, handler_out

    # Disarm trigger 0 before touching memory.
    csrw 0x7a0, zero
    csrw 0x7a1, zero

    # Now writing is safe.
    la   s10, fire_count
    lw   s11, 0(s10)
    addi s11, s11, 1
    sw   s11, 0(s10)

    csrr s10, mepc
    addi s10, s10, 4
    csrw mepc, s10

handler_out:
    mret

    .data
    .align 2
fire_count:
    .word 0
watched_word:
    .word 0
other_word:
    .word 0
