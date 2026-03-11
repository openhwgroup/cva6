// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

.section .text._start

.global _start
.align 4
_start:
  li   x1, 0
  li   x2, 0
  li   x3, 0
  li   x4, 0
  li   x5, 0
  li   x6, 0
  li   x7, 0
  li   x8, 0
  li   x9, 0
  li   x10, 0
  li   x11, 0
  li   x12, 0
  li   x13, 0
  li   x14, 0
  li   x15, 0
  li   x16, 0
  li   x17, 0
  li   x18, 0
  li   x19, 0
  li   x20, 0
  li   x21, 0
  li   x22, 0
  li   x23, 0
  li   x24, 0
  li   x25, 0
  li   x26, 0
  li   x27, 0
  li   x28, 0
  li   x29, 0
  li   x30, 0
  li   x31, 0

  // Init stack and global pointer with safe, linked values
  la   sp, __stack_pointer$
  .option push
  .option norelax
  la   gp, __global_pointer$
  .option pop

  // Set trap handler
  la   t0, __trap_handler
  csrw mtvec, t0

  // Check boot mode
  la   t0, __base_regs
  lw   t1, 0(t0)
  bne  t1, zero, __boot_spm

__boot_dram:
  csrr a0, mhartid
  la   t0, __base_dram
  jalr ra, 0(t0)
  j    _exit

__boot_spm:
  csrr a0, mhartid
  la   t0, __base_spm
  jalr ra, 0(t0)

// If main returns, we end up here
.global _exit
_exit:
  // Set EOC, then wait forever
  slli a0, a0, 1
  ori  a0, a0, 1
  la   t0, __base_regs
  sw   a0, 4(t0)
1:
  wfi
  j    1b

.align 8
__trap_handler:
  csrr t0, mcause
1:
  wfi
  j 1b
