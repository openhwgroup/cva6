// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

.section .text._start

.global _start
.align 4
_start:

    // Clear all registers
    li x2,  0
    li x3,  0
    li x4,  0
    li x5,  0
    li x6,  0
    li x7,  0
    li x8,  0
    li x9,  0
    li x10, 0
    li x11, 0
    li x12, 0
    li x13, 0
    li x14, 0
    li x15, 0
    li x16, 0
    li x17, 0
    li x18, 0
    li x19, 0
    li x20, 0
    li x21, 0
    li x22, 0
    li x23, 0
    li x24, 0
    li x25, 0
    li x26, 0
    li x27, 0
    li x28, 0
    li x29, 0
    li x30, 0
    li x31, 0

    // Init stack and global pointer with safe, linked values
    la sp, __stack_pointer$
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop

    // Clear .bss
    la t0, __bss_start
    la t1, __bss_end
1:
    bgeu t0, t1, 2f
    sd   zero, 0(t0)
    addi t0, t0, 8
    j    1b
2:

    // Set up trap handler
    la    t0, trap_handler
    csrw  mtvec, t0

    // Call main
    tail main

    // Should never get here
    ret

.weak main
main:
    li a0, 0
    ret

.align 8
.globl trap_handler
trap_handler:
  // An unexpected trap ends the test with a failing return code: 0x100 plus the
  // low byte of mcause, plus 0x200 for an interrupt
  csrr t0, mcause
  andi a0, t0, 0xff
  ori  a0, a0, 0x100
  bgez t0, 1f
  ori  a0, a0, 0x200
1:
  slli a0, a0, 1
  ori  a0, a0, 1
  la   t0, __base_regs
  sw   a0, 4(t0)
2:
  wfi
  j    2b
