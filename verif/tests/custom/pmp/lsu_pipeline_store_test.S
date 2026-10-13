// Copyright 2026 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

    .equ STORE_ACCESS_FAULT, 7
    .equ MSTATUS_MPP,       0x00001800
    .equ MSTATUS_MPRV,      0x00020000
    .equ MSTATUS_MPP_S,     0x00000800
    .equ SATP_MODE_SV39,    0x8000000000000000

    .equ DENIED_PADDR,      0x90000000
    .equ ALLOWED_PADDR,     0x80000000
    .equ DENIED_VADDR,      0x50000000
    .equ ALLOWED_VADDR,     0x40000000
    .equ INITIAL_VALUE,     0x13579bdf
    .equ STORE_VALUE,       0x2468ace0

    .section .text
    .globl main
main:
    // Initialize the location before locking its PMP entry.
    li t1, DENIED_PADDR
    li t2, INITIAL_VALUE
    sw t2, 0(t1)

    // Entry 0 allows [0, 0x90000000), entry 1 makes
    // [0x90000000, 0x90001000) locked and read-only, and entry 2 allows the
    // remainder through 0xc0000000.  The surrounding entries allow S-mode
    // page-table walks and the load paired with each denied store.
    li t0, 0x24000000
    csrw pmpaddr0, t0
    li t0, 0x24000400
    csrw pmpaddr1, t0
    li t0, 0x30000000
    csrw pmpaddr2, t0
    li t0, 0x000f890f
    csrw pmpcfg0, t0

    la t0, trap_count
    sw zero, 0(t0)

#ifdef PMP_NO_MMU
    // Exercise the no-MMU response path.
    li t0, DENIED_PADDR
    call set_expected_tval
    li t1, DENIED_PADDR
    li t2, STORE_VALUE
    li t4, ALLOWED_PADDR
    .option push
    .option norvc
    sw t2, 0(t1)
    lw t3, 0(t4)
    .option pop
    li t0, 1
    call check_result
#else
    // Install a one-GiB Sv39 leaf mapping [0x40000000, 0x80000000) to
    // [0x80000000, 0xc0000000).  DENIED_VADDR therefore translates to the
    // PMP-protected DENIED_PADDR.
    la t0, root_page_table
    srli t0, t0, 12
    li t1, SATP_MODE_SV39
    or t0, t0, t1
    csrw satp, t0

    // Flush the DTLB so that the denied store itself takes the miss/PTW path.
    sfence.vma
    li t0, DENIED_VADDR
    call set_expected_tval
    call enable_s_data_translation
    li t1, DENIED_VADDR
    li t2, STORE_VALUE
    li t4, ALLOWED_VADDR
    .option push
    .option norvc
    sw t2, 0(t1)
    lw t3, 0(t4)
    .option pop
    call disable_data_translation
    li t0, 1
    call check_result

    // Refill the DTLB with an allowed read, then repeat the adjacent
    // denied-store/allowed-load sequence on the hit path.
    sfence.vma
    li t0, DENIED_VADDR
    call set_expected_tval
    call enable_s_data_translation
    li t1, DENIED_VADDR
    lw t3, 0(t1)
    li t2, STORE_VALUE
    li t4, ALLOWED_VADDR
    .option push
    .option norvc
    sw t2, 0(t1)
    lw t3, 0(t4)
    .option pop
    call disable_data_translation
    li t0, 2
    call check_result
#endif

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

enable_s_data_translation:
    li t0, MSTATUS_MPP | MSTATUS_MPRV
    csrc mstatus, t0
    li t0, MSTATUS_MPP_S | MSTATUS_MPRV
    csrs mstatus, t0
    ret

disable_data_translation:
    li t0, MSTATUS_MPRV
    csrc mstatus, t0
    ret

check_result:
    la t1, trap_count
    lw t1, 0(t1)
    bne t0, t1, fail
    li t1, DENIED_PADDR
    lw t1, 0(t1)
    li t2, INITIAL_VALUE
    bne t1, t2, fail
    ret

    .globl handle_trap
handle_trap:
    li t0, MSTATUS_MPRV
    csrc mstatus, t0

    li t0, STORE_ACCESS_FAULT
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

    .section .data
    .align 3
expected_tval:
    .dword 0
trap_count:
    .word 0

#ifndef PMP_NO_MMU
    // Sv39 root entry 1 is a one-GiB leaf with PPN 0x80000 and V/R/W/X/A/D.
    .section .page_table, "aw", @progbits
    .balign 4096
root_page_table:
    .dword 0
    .dword 0x00000000200000cf
    .rept 510
    .dword 0
    .endr
#endif
