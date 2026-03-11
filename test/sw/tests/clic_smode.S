// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// Test CLIC interrupt controller.
//
// Test the correct handling of interrupts when executing in different
// privilege modes. Check the following cases:
// - Interrupts delegated to S-mode are not taken when executing in M-mode.
// - Interrupts delegated to S-mode are taken when executing in S-mode.

#define xstr(s) str(s)
#define str(s) s
#define CLIC_BASE                     0x10040000
#define CLIC_CLICCFG_REG              (CLIC_BASE + 0x0)
#define CLIC_CLICCFG_NLBITS_OFFSET    (0)
#define CLIC_CLICCFG_NMBITS_OFFSET    (4)
#define CLIC_CLICINT_REG(id)          (CLIC_BASE + 0x1000 + 0x4 * id)
#define CLIC_CLICINT_IP_OFFSET        (0)
#define CLIC_CLICINT_IP_MASK          (1)
#define CLIC_CLICINT_IE_OFFSET        (8)
#define CLIC_CLICINT_IE_MASK          (1)
#define CLIC_CLICINT_ATTR_SHV_OFFSET  (16)
#define CLIC_CLICINT_ATTR_SHV_MASK    (1)
#define CLIC_CLICINT_ATTR_TRIG_OFFSET (17)
#define CLIC_CLICINT_ATTR_TRIG_MASK   (0x3)
#define CLIC_CLICINT_ATTR_MODE_OFFSET (22)
#define CLIC_CLICINT_ATTR_MODE_MASK   (0x3)
#define CLIC_CLICINT_CTL_OFFSET       (24)
#define CLIC_CLICINT_CTL_MASK         (0xff)

#define MINTTHRESH                    (0x347)
#define MTVT                          (0x307)

#define TEST_IRQ_LINE                 (31)

#define SMODE                         (1)
#define MMODE                         (3)

#define WAIT(N) \
  li a0, (N); \
  jal wait

// Wait task: perform busy loop.
// Number of iterations is passed in a0.
wait:
  mv   t0, a0
1:
  addi t0, t0, -1
  bnez t0, 1b

  ret

// Enable an interrupt line on the CLIC.
// Interrupt line number is passed in a0.
// Interrupt privilege mode is passed in a1.
enable_interrupt:

  // Compute interrupt's clicint base address
  mv   s2, a0
  slli s2, s2, 2
  li   s1, CLIC_CLICINT_REG(0)
  add  s2, s2, s1

  // Set trigger type to edge-triggered
  mv   t0, s2
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_ATTR_TRIG_OFFSET
  or   t1, t1, t2
  // Set privilege mode
  li   t2, CLIC_CLICINT_ATTR_MODE_MASK
  slli t2, t2, CLIC_CLICINT_ATTR_MODE_OFFSET
  not  t2, t2
  and  t1, t1, t2
  slli t2, a1, CLIC_CLICINT_ATTR_MODE_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // Set interrupt level and priority
  mv   t0, s2
  lw   t1, 0(t0)
  li   t2, 0xaa << CLIC_CLICINT_CTL_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // Enable interrupt
  mv   t0, s2
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_IE_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  ret

// Trigger an interrupt line on the CLIC.
// Interrupt line number is passed in a0.
trigger_interrupt:

  // Compute interrupt's clicint base address
  mv   s2, a0
  slli s2, s2, 2
  li   s1, CLIC_CLICINT_REG(0)
  add  s2, s2, s1

  // Trigger interrupt via SW
  mv   t0, s2
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_IP_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  ret

// Restore mtvec and return 0 (PASS)
pass_restore:
  csrw mtvec, s0
  li a0, 0
  j exit

// Restore mtvec and return 1 (FAIL)
fail_restore:
  csrw mtvec, s0
  li a0, 1
  j exit

// Enviroment call to M-mode. By default,
// return value is passed in a0. Return PASS.
smode_pass:
  li a0, 0
  ecall

// Enviroment call to M-mode. By default,
// return value is passed in a0. Return FAIL.
smode_fail:
  li a0, 1
  ecall

// Return to runtime environment.
// Return address was saved in mscratch
exit:
  csrr ra, mscratch
  ret

.align
.option norvc
.global main
main:

  // Save return address
  csrw mscratch, ra

  // Enable interrupts (set mstatus.mie)
  csrsi mstatus, 0x8

  // Activate CLIC mode
  la t0, mtvec_handler_fail
  ori t0, t0, 0x3
  csrrw s0, mtvec, t0

  // CLIC configuration
  // Set number of bits for level and privilege mode encoding
  li   t0, CLIC_CLICCFG_REG
  li   t1, 0x4 << CLIC_CLICCFG_NLBITS_OFFSET
  li   t2, 0x3 << CLIC_CLICCFG_NMBITS_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // Set interrupt threshold to zero
  li   a0, 0x1
  csrw MINTTHRESH, zero

  /////////////////////////////////////
  //              Test 1             //
  /////////////////////////////////////
  // Delegate interrupt line to S-mode and
  // check that it does not trigger while
  // executing in M-mode
  li  a0, TEST_IRQ_LINE
  li  a1, SMODE
  jal enable_interrupt
  WAIT(500)
  li  a0, TEST_IRQ_LINE
  jal trigger_interrupt
  WAIT(500)

  /////////////////////////////////////
  //              Test 2             //
  /////////////////////////////////////
  // Jump to S-mode and check that the same
  // interrupt when triggered is taken

  // mret will jump to the address in mepc
  la   t0, smode_entry
  csrw mepc, t0
  // Set up PMPs
  li   t0, -1
  srli t0, t0, 2
  csrw pmpaddr0, t0   // top of TOR range
  li   t0, 0x0f       // R=1 W=1 X=1 A=TOR(01)
  csrw pmpcfg0, t0
  // Set mstatus.MPP to 01 (S-mode)
  li   t0, 0x800
  csrs mstatus, t0
  mret

  j fail_restore


// S-mode entry point.
// Set up interrupt handler and enable interrupts.
// Interrupt was set pending already and should
// trigger immediately after interrupts are enabled.
smode_entry:

  // Write interrupt handler
  la    t0, stvec_handler_succeed
  ori   t0, t0, 0x3
  csrrw s0, stvec, t0

  // Enable interrupts (set sstatus.sie)
  csrsi sstatus, 0x2

  WAIT(100)

  // Should not reach here
  j smode_fail


// Check return value from S-mode
// (by convention stored in a0)
// and succeed or fail accordingly.
check_smode_return:
  beqz a0, pass_restore
  j fail_restore

.align 8
.global mtvec_handler_fail
mtvec_handler_fail:
  csrr t0, mcause
  li   t1, 1 << 63
  and  t0, t0, t1
  beqz t0, check_smode_return
  j fail_restore

.align 8
.global mtvec_handler_succeed
mtvec_handler_succeed:
  csrr t0, mcause
  li   t1, 1 << 63
  and  t0, t0, t1
  beqz t0, check_smode_return
  j pass_restore

.align 8
.global stvec_handler_fail
stvec_handler_fail:
  j smode_fail

.align 8
.global stvec_handler_succeed
stvec_handler_succeed:
  j smode_pass

.data
