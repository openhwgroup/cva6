// Copyright 2026 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

    .equ LOAD_ACCESS_FAULT,       5
    .equ HLVX_RESULT_SENTINEL,    0x5a5a5a5a5a5a5a5a

    .option arch, +h
    .section .text
    .globl main
main:
    // Entry 0 is a locked, read-only four-KiB NAPOT region.  Entry 1
    // allows all other accesses.  HLVX must require execute permission even
    // with address translation disabled and the instruction running in M-mode.
    la t0, target_read_only
    srli t0, t0, 2
    ori t0, t0, 0x1ff
    csrw pmpaddr0, t0
    li t0, -1
    csrw pmpaddr1, t0
    li t0, 0x00001f99
    csrw pmpcfg0, t0

    la t0, trap_count
    sw zero, 0(t0)

    // Ordinary loads from the read-only region must still succeed when an
    // executable HLVX request follows immediately.  This checks that a later
    // request cannot impose execute permission on the earlier response.
    la t0, target_read_only
    la t2, allowed_data
    .option push
    .option norvc
    ld t3, 0(t0)
    hlvx.hu t4, (t2)
    .option pop
    li t0, 0x1234
    bne t3, t0, fail
    li t0, 0x5678
    bne t4, t0, fail
    li t0, 0
    call check_trap_count

    // A denied HLVX must fault with its own tval and leave its destination
    // unchanged, even when the next request is an ordinary allowed load.
    la t0, target_read_only
    call set_expected_tval
    li t3, HLVX_RESULT_SENTINEL
    la t2, allowed_data
    .option push
    .option norvc
    hlvx.hu t3, (t0)
    ld t4, 0(t2)
    .option pop
    li t0, 1
    call check_trap_count
    li t0, HLVX_RESULT_SENTINEL
    bne t3, t0, fail

pass:
    li a0, 0
    tail exit

fail:
    li a0, 1
    tail exit

set_expected_tval:
    la t1, expected_tval
    sd t0, 0(t1)
    ret

check_trap_count:
    la t1, trap_count
    lw t1, 0(t1)
    bne t0, t1, fail
    ret

    .globl handle_trap
handle_trap:
    li t0, LOAD_ACCESS_FAULT
    bne a0, t0, trap_fail

    csrr t0, mtval
    la t1, expected_tval
    ld t1, 0(t1)
    bne t0, t1, trap_fail

    la t0, trap_count
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)

    // crt.S writes the returned address to mepc before executing mret.
    addi a0, a1, 4
    ret

trap_fail:
    li a0, 1
    tail exit

    .section .data, "aw", @progbits
    .align 3
expected_tval:
    .dword 0
trap_count:
    .word 0
    .align 3
allowed_data:
    .dword 0x5678

    .balign 4096
target_read_only:
    .dword 0x1234
