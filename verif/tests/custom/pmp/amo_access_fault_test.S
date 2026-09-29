// Copyright 2026 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

    .equ STORE_AMO_ACCESS_FAULT, 7
    .equ AMO_RESULT_SENTINEL,    0x5a5a5a5a5a5a5a5a

    .section .text
    .globl main
main:
    // Entry 0 is a locked four-KiB NAPOT region with no permissions.  Entry 1
    // covers the remaining address space so that the load adjacent to the AMO
    // is allowed.
    la t0, target_no_access
    srli t0, t0, 2
    ori t0, t0, 0x1ff
    csrw pmpaddr0, t0
    li t0, -1
    csrw pmpaddr1, t0
    li t0, 0x00001f98
    csrw pmpcfg0, t0

    la t0, trap_count
    sw zero, 0(t0)

    // A PMP-denied AMO must report a store/AMO access fault, not a load
    // access fault.  Keep an allowed load immediately behind it to expose
    // request/response access-type and tval misalignment.
    la t0, target_no_access
    call set_expected_tval
    li t1, 1
    li t3, AMO_RESULT_SENTINEL
    la t2, allowed_data
    .option push
    .option norvc
    amoadd.d t3, t1, (t0)
    ld t4, 0(t2)
    .option pop
    li t0, 1
    call check_trap_count
    li t0, AMO_RESULT_SENTINEL
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
    li t0, STORE_AMO_ACCESS_FAULT
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
    .dword 0

    .balign 4096
target_no_access:
    .dword 0
