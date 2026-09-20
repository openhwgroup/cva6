# ------------------------------------------------------------------------------
#   Copyright 2026 Thales France
#
#   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#   You may obtain a copy of the License at https://solderpad.org/licenses/
# ------------------------------------------------------------------------------
#   be_swap_test.S
#
#   Exercises the big endian data path. mstatus.MBE selects whether the core
#   treats data memory as big endian; the core stays little endian internally
#   and reverses the byte order as data crosses the load and store boundary.
#
#   The test is built little endian like every other one, and toggles MBE at
#   run time rather than relying on a big endian binary. Mixing the two would
#   cancel out: the compiler would lay the constants out reversed and the core
#   would reverse them back. Toggling MBE alone isolates the swappers.
#
#   What it checks:
#     1. A word stored and loaded back with MBE set reads its own value. Both
#        halves of the round trip swap, so they cancel and the value returns
#        unchanged. This fails if only one direction swaps.
#     2. A word stored with MBE set and read back with MBE clear comes out
#        byte reversed. This is the discriminating check: it fails if the
#        store swapper does nothing.
#     3. A byte access is never swapped, whatever MBE says.
#     4. mstatush reads back the MBE bit, and clearing it restores little
#        endian behaviour.
#
#   MBE is cleared before returning. The tohost protocol the testbench watches
#   is little endian, so a test that exits with MBE set would write a value the
#   tracer cannot read.
#
#   RV32 only: mstatush exists on RV32, where the high half of mstatus is a
#   separate CSR. On RV64 the MBE bit lives in mstatus itself and this test
#   would have to write it there instead.
# ------------------------------------------------------------------------------

#include "encoding.h"

#define MSTATUSH      0x310
#define MSTATUSH_MBE  0x20

    .text
    .globl main
main:

#if __riscv_xlen == 32

    # --------------------------------------------------------------------
    # Scenario 4a: MBE reads back what was written
    # --------------------------------------------------------------------
    li    t0, MSTATUSH_MBE
    csrs  MSTATUSH, t0
    csrr  t1, MSTATUSH
    and   t2, t1, t0
    beqz  t2, fail              # the bit did not stick

    # --------------------------------------------------------------------
    # Scenario 1: a round trip under MBE returns the value unchanged
    # Both the store and the load swap, so the two cancel.
    # --------------------------------------------------------------------
    la    t3, scratch
    li    t4, 0x12345678
    sw    t4, 0(t3)
    lw    t5, 0(t3)
    bne   t5, t4, fail

    # --------------------------------------------------------------------
    # Scenario 3: a byte is never swapped
    # --------------------------------------------------------------------
    li    t4, 0xA5
    sb    t4, 4(t3)
    lbu   t5, 4(t3)
    bne   t5, t4, fail

    # --------------------------------------------------------------------
    # Scenario 2: stored under MBE, read back without it, byte reversed
    # This is what tells a working store swapper from a missing one.
    # --------------------------------------------------------------------
    la    t3, scratch
    li    t4, 0x12345678
    sw    t4, 8(t3)

    li    t0, MSTATUSH_MBE
    csrc  MSTATUSH, t0          # back to little endian

    lw    t5, 8(t3)
    li    t6, 0x78563412        # 0x12345678 with its bytes reversed
    bne   t5, t6, fail

    # --------------------------------------------------------------------
    # Scenario 4b: with MBE clear the round trip is plain again
    # --------------------------------------------------------------------
    li    t4, 0x0BADCAFE
    sw    t4, 12(t3)
    lw    t5, 12(t3)
    bne   t5, t4, fail

    # MBE reads back clear
    csrr  t1, MSTATUSH
    andi  t2, t1, MSTATUSH_MBE
    bnez  t2, fail

#endif

pass:
    li    a0, 0
    ret

fail:
    # leave the core little endian whatever happens, so the exit path works
    li    t0, MSTATUSH_MBE
    csrc  MSTATUSH, t0
    li    a0, 1
    ret

    .data
    .align 6
scratch:
    .zero 64
