# ------------------------------------------------------------------------------
#   Copyright 2026 Thales France
#
#   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#   You may obtain a copy of the License at https://solderpad.org/licenses/
# ------------------------------------------------------------------------------
#   sdtrig_mcontrol6_load_data.S
#
#   mcontrol6 load trigger with select = 1, comparing the value the load brought
#   back rather than the address it came from.
#
#   This is the one imprecise trigger the CVA6 documentation describes, and the
#   reason is physical: the value does not exist until the load has returned, so
#   the break cannot happen before the instruction. It lands on the one after,
#   which is what the timing field of the exception carries through the
#   scoreboard and the commit stage.
#
#   The test checks exactly that: the destination register must hold the loaded
#   value when the handler runs. A precise trigger would have stopped the load
#   and left the register alone, and that difference is the whole point of
#   separating this case from the address one.
#
#   tdata1 layout for mcontrol6 on RV32, as the module decodes it:
#     [31:28] type = 6      [22] hit0     [21] select    [18:16] size
#     [15:12] action        [11] chain    [10:7] match   [6] m
#     [4] s   [3] u   [2] execute   [1] store   [0] load
#
#   Requires Sdtrig, SdtrigMcontrol6 and SdtrigMcontrol6LoadData.
# ------------------------------------------------------------------------------

    .text
    .option norvc

    .globl main
main:
    la   t0, trap_handler
    csrw mtvec, t0
    la   t0, break_count
    sw   zero, 0(t0)
    la   t0, seen_value
    sw   zero, 0(t0)

    # --------------------------------------------------------------------
    # Watch the value 0xCAFEBABE, which watched_word holds, then load it.
    # --------------------------------------------------------------------
    li   t0, 0
    csrw 0x7a0, t0              # tselect = 0

    li   t1, 0xCAFEBABE
    csrw 0x7a2, t1              # tdata2 = the value to watch for

    # type 6, match 0, m in [6], load in [0], action 0, select = 1 in [21]
    li   t1, 0x60200041
    csrw 0x7a1, t1

    li   a4, 0x5A5A5A5A         # sentinel, must be overwritten by the load
    la   t0, watched_word
    lw   a4, 0(t0)              # brings back the watched value
    nop                         # the deferred break lands here

    la   t0, break_count
    lw   t1, 0(t0)
    beqz t1, fail               # the value comparison never fired

    # The break being deferred, the load completed: the register holds the
    # value, not the sentinel.
    li   t2, 0xCAFEBABE
    bne  a4, t2, fail           # the load was stopped: not a deferred break

    # --------------------------------------------------------------------
    # A load of a value the trigger is not watching must not fire.
    # --------------------------------------------------------------------
    la   t0, break_count
    sw   zero, 0(t0)

    li   t0, 0
    csrw 0x7a0, t0
    li   t1, 0xCAFEBABE
    csrw 0x7a2, t1
    li   t1, 0x60200041
    csrw 0x7a1, t1

    la   t0, other_word         # holds 0x11112222
    lw   a6, 0(t0)
    nop
    nop

    # Disarm: keep the type, drop the operation bits.
    li   t1, 0x60200040
    csrw 0x7a1, t1

    la   t0, break_count
    lw   t1, 0(t0)
    bnez t1, fail               # fired on a value it was not watching

    li   t2, 0x11112222
    bne  a6, t2, fail           # that load was supposed to go through

    # --------------------------------------------------------------------
    li a0, 0
    ret

fail:
    li   t1, 0x60200040         # keep the type, drop the operation bits
    csrw 0x7a1, t1
    li a0, 1
    ret

    # --------------------------------------------------------------------
    # Counts breakpoints, disarms the trigger, steps over the instruction the
    # break landed on. s10 and s11 are scratch, main does not use them.
    # --------------------------------------------------------------------
    .align 6
trap_handler:
    li   s10, 0x60200040        # type 6 kept, load/store/execute cleared
    csrw 0x7a0, zero
    csrw 0x7a1, s10

    csrr s10, mcause
    li   s11, 3                 # breakpoint
    bne  s10, s11, handler_out

    la   s10, break_count
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
break_count:
    .word 0
seen_value:
    .word 0
watched_word:
    .word 0xCAFEBABE
other_word:
    .word 0x11112222
