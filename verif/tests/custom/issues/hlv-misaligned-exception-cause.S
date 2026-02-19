# Copyright 2025 Hexaplex AI
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yaron Dinkin (yaron@hexaplex.com)
#
#*****************************************************************************
# hlv-misaligned-exception-cause.S
#-----------------------------------------------------------------------------
#
# Test Description:
#   Exercises hlv.d with an 8-byte misaligned address while running in HS-mode
#   (S-mode with the hypervisor extension enabled). The trap handler records
#   scause and ensures the exception code is CAUSE_MISALIGNED_LOAD (0x4).
#   Any other behavior causes the test to fail.

#include "encoding.h"

.equ STATUS_PASS,                0
.equ STATUS_NO_TRAP,             1
.equ STATUS_WRONG_CAUSE,         2
.equ STATUS_UNEXPECTED_TRAP,     3

.section .text
.globl main
main:
  la   t0, observed_scause
  sd   x0, 0(t0)
  la   t0, s_trap_count
  sd   x0, 0(t0)
  la   t0, s_test_status
  sd   x0, 0(t0)

  csrw satp, x0

  # Allow HS/S-mode to execute and access the full physical address space.
  li   t0, -1
  csrw pmpaddr0, t0
  li   t0, 0x0F
  csrw pmpcfg0, t0
  sfence.vma

  la   t0, s_trap_handler
  csrw stvec, t0

  csrr t0, medeleg
  li   t1, (1 << CAUSE_MISALIGNED_LOAD)
  or   t0, t0, t1
  csrw medeleg, t0

  la   t0, s_mode_entry
  li   t1, MSTATUS_MPP
  csrc mstatus, t1
  li   t1, (PRV_S << 11)
  csrs mstatus, t1
  csrw mepc, t0
  mret

main_post_s_mode:
  la   t0, s_test_status
  ld   t1, 0(t0)
  beqz t1, pass
  mv   a0, t1
  jal  exit

pass:
  li   a0, 0
  jal  exit

.align 2
.globl handle_trap
handle_trap:
  addi sp, sp, -32
  sd   ra, 24(sp)
  sd   t0, 16(sp)
  sd   t1, 8(sp)
  sd   t2, 0(sp)

  la   t2, observed_mcause
  sd   a0, 0(t2)

  li   t0, CAUSE_SUPERVISOR_ECALL
  beq  a0, t0, handle_trap_ecall

  la   t0, s_test_status
  li   t1, STATUS_UNEXPECTED_TRAP
  sd   t1, 0(t0)
  la   t0, main_post_s_mode
  mv   a0, t0
  j    handle_trap_ret

handle_trap_ecall:
  la   t0, main_post_s_mode
  mv   a0, t0

handle_trap_ret:
  ld   t2, 0(sp)
  ld   t1, 8(sp)
  ld   t0, 16(sp)
  ld   ra, 24(sp)
  addi sp, sp, 32
  ret

.align 2
s_mode_entry:
  la   sp, s_mode_stack_top

  li   x10, 0x8fffffdc
  li   x14, 0
  hlv.d x14, 0(x10)

s_after_fault:
  la   t0, s_trap_count
  ld   t1, 0(t0)
  beqz t1, s_fail_no_trap
  li   t2, 1
  bne  t1, t2, s_fail_unexpected_trap

  la   t0, observed_scause
  ld   t1, 0(t0)
  li   t2, CAUSE_MISALIGNED_LOAD
  bne  t1, t2, s_fail_wrong_cause

s_pass:
  li   t0, STATUS_PASS
  j    s_finish

s_fail_no_trap:
  li   t0, STATUS_NO_TRAP
  j    s_finish

s_fail_unexpected_trap:
  li   t0, STATUS_UNEXPECTED_TRAP
  j    s_finish

s_fail_wrong_cause:
  li   t0, STATUS_WRONG_CAUSE

s_finish:
  la   t1, s_test_status
  sd   t0, 0(t1)
  ecall

.align 2
s_trap_handler:
  addi sp, sp, -48
  sd   ra, 40(sp)
  sd   t0, 32(sp)
  sd   t1, 24(sp)
  sd   t2, 16(sp)
  sd   t3, 8(sp)
  sd   t4, 0(sp)

  csrr t0, scause
  la   t1, observed_scause
  sd   t0, 0(t1)

  la   t1, s_trap_count
  ld   t2, 0(t1)
  addi t2, t2, 1
  sd   t2, 0(t1)

  csrr t3, sepc
  addi t3, t3, 4
  csrw sepc, t3

  ld   t4, 0(sp)
  ld   t3, 8(sp)
  ld   t2, 16(sp)
  ld   t1, 24(sp)
  ld   t0, 32(sp)
  ld   ra, 40(sp)
  addi sp, sp, 48
  sret

.section .data
.align 3
observed_scause:
  .dword 0
observed_mcause:
  .dword 0
s_trap_count:
  .dword 0
s_test_status:
  .dword 0

.section .bss
.align 7
s_mode_stack:
  .space 512
s_mode_stack_top:

