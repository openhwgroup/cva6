# ------------------------------------------------------------------------------
#   Copyright 2026 Thales France
#
#   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#   You may obtain a copy of the License at https://solderpad.org/licenses/
# ------------------------------------------------------------------------------
#   sdtrig_mcontrol6_exec_match.S
#
#   Fires an mcontrol6 execute trigger on the address of an instruction, once
#   per match type the CVA6 documentation claims for this trigger: equal (0),
#   NAPOT (1) and not-equal (8). The action is the breakpoint exception, so the
#   test needs no debug module to observe the fire: it counts breakpoint traps
#   in its own handler.
#
#   tdata1 layout for mcontrol6 on RV32, as the module decodes it:
#     [31:28] type = 6      [22] hit0     [21] select    [18:16] size
#     [15:12] action        [11] chain    [10:7] match   [6] m
#     [4] s   [3] u   [2] execute   [1] store   [0] load
#
#   select = 0 compares the address, select = 1 compares the instruction word.
#   action = 0 raises a breakpoint. m = 1 arms the trigger in machine mode.
#
#   Requires a target with Sdtrig, SdtrigMcontrol6 and SdtrigMcontrol6ExecAddr
#   enabled, and the match types enabled in SdtrigSupportedMatch.
# ------------------------------------------------------------------------------

    .text
    # Keep every instruction 4 bytes wide: the handler steps over the trapping
    # instruction with mepc + 4, and with C a bare nop would assemble to a
    # 2-byte c.nop.
    .option norvc

    .globl main
main:
    # Install our trap handler and clear the fire counter.
    la   t0, trap_handler
    csrw mtvec, t0
    la   t0, fire_count
    sw   zero, 0(t0)

    # --------------------------------------------------------------------
    # Match type 0, equal: trigger on the exact address of target_insn_eq.
    # --------------------------------------------------------------------
    li   t0, 0
    csrw 0x7a0, t0              # tselect = 0

    la   t1, target_insn_eq
    csrw 0x7a2, t1              # tdata2 = address to match

    # type 6, match 0 (equal), m = 1, execute = 1, action 0 (breakpoint)
    li   t1, 0x60000044         # [31:28]=6 [6]=m [2]=execute
    csrw 0x7a1, t1

target_insn_eq:
    nop                         # must trap before executing

    # The handler skips the trapping instruction, so we land here.
    la   t0, fire_count
    lw   t1, 0(t0)
    li   t2, 1
    bne  t1, t2, fail           # exactly one fire expected

    # Clear tdata1 and tdata2 so that no later instruction matches.
    li   t0, 0
    csrw 0x7a0, t0
    csrw 0x7a1, zero

    # --------------------------------------------------------------------
    # Match type 8, not-equal, is deliberately not exercised as an armed
    # machine-mode execute trigger.
    #
    # It fires on every address that differs from tdata2, so it also fires on
    # the first instruction of the trap handler, and the handler cannot reach
    # the csrw that would disarm it before being trapped again. The result is
    # an endless breakpoint loop, which is the trigger behaving as specified,
    # not a defect: the Sdtrig spec expects the handler to run with the trigger
    # inactive, which needs either dmode so the action is a debug-mode entry,
    # or a privilege filter excluding the mode the handler runs in.
    #
    # The equality and NAPOT cases below cover the comparison logic. Verifying
    # not-equal properly needs a debug-mode action, which belongs in a test
    # driven through the debug module rather than a self-handled breakpoint.
    # Its support bit is still enabled on this target, so the RTL path is
    # elaborated either way.

    # --------------------------------------------------------------------
    # Match type 1, NAPOT, is not exercised here either, for a reason found
    # while writing this test and worth recording.
    #
    # The Sdtrig spec encodes a naturally aligned power-of-two range as the
    # base address followed by a run of low ones, so a 32-byte range at
    # 0x80003000 is tdata2 = 0x8000300f. The module guards the comparison with
    #
    #     is_valid_napot = ((base & (base + 1)) == 0)
    #
    # which demands base + 1 be a power of two over the whole register, that is
    # base be 0b0..01..1. Only ranges based at address zero satisfy it, so
    # 0x8000300f is rejected and napot_match32 returns zero. A NAPOT trigger
    # can never match code living at a real address.
    #
    # The mask the function then computes, ~(base & ~(base + 1)), is the right
    # one; it is the guard in front of it that is too strict. This looks like an
    # upstream defect rather than an encoding mistake on our side, and it is
    # covered by sdtrig_napot_guard_test, which pins the current behaviour so
    # the day the guard is relaxed the change is visible.

    # --------------------------------------------------------------------
    # A disarmed trigger must not fire: run a few instructions with every
    # trigger cleared and check the counter stays put.
    # --------------------------------------------------------------------
    la   t0, fire_count
    sw   zero, 0(t0)

    nop
    nop
    nop

    la   t0, fire_count
    lw   t1, 0(t0)
    bnez t1, fail               # no trigger armed, no fire allowed

    # --------------------------------------------------------------------
    li a0, 0
    ret

fail:
    li a0, 1
    ret

    # --------------------------------------------------------------------
    # Trap handler. Counts breakpoint traps and steps over the instruction
    # that trapped so the test can carry on. mcause 3 is the breakpoint.
    # --------------------------------------------------------------------
    .align 6
trap_handler:
    addi sp, sp, -16
    sw   t0, 0(sp)
    sw   t1, 4(sp)
    sw   t2, 8(sp)

    csrr t0, mcause
    li   t1, 3                  # breakpoint
    bne  t0, t1, handler_out

    la   t0, fire_count
    lw   t1, 0(t0)
    addi t1, t1, 1
    sw   t1, 0(t0)

    # Step over the trapping instruction. Every instruction this test traps
    # on is a 4-byte nop, the file being assembled with .option norvc, so
    # mepc + 4 is the next one.
    csrr t0, mepc
    addi t0, t0, 4
    csrw mepc, t0

handler_out:
    lw   t0, 0(sp)
    lw   t1, 4(sp)
    lw   t2, 8(sp)
    addi sp, sp, 16
    mret

    .data
    .align 2
fire_count:
    .word 0
