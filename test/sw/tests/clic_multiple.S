// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Nils Wistoff <nwistoff@iis.ee.ethz.ch>
//
// Test clic.
//
// Queues two software interrupts with different interrupt levels. The lower
// level interrupt is queued first. Then raises the threshold to a level which is
// between those two interrupts. Only the latter interrupt should fire and be
// handled.

#define xstr(s) str(s)
#define str(s) s
#define CLIC_BASE                     0x10040000
#define CLIC_CLICCFG_REG              (CLIC_BASE + 0x0)
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

.align
.option norvc
.global main
main:
  .macro clic_enable_irq id ctl

  // Set shv of irq
  li   t0, CLIC_CLICINT_REG(\id)
  li   t1, 1 << CLIC_CLICINT_ATTR_SHV_OFFSET
  sw   t1, 0(t0)

  // set trigger type to edge-triggered of irq
  li   t0, CLIC_CLICINT_REG(\id)
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_ATTR_TRIG_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // enable irq via SW by writing to clicintip
  li   t0, CLIC_CLICINT_REG(\id)
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_IP_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // set interrupt level and priority for interrupt
  li   t0, CLIC_CLICINT_REG(\id)
  lw   t1, 0(t0)
  li   t2, \ctl << CLIC_CLICINT_CTL_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // enable interrupt
  li   t0, CLIC_CLICINT_REG(\id)
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_IE_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  .endm


.align 2
.option norvc
1:
  // Enable interrupts (set mstatus.mie)
  csrsi mstatus, 0x8

  // Activate CLIC mode
  la t0, mtvec_handler_fail
  ori t0, t0, 0x3
  csrrw s0, mtvec, t0

  // Write mtvt base
  la t0, mtvt_handler
  csrw MTVT, t0

  // set number of bits for level encoding
  li   t0, CLIC_CLICCFG_REG
  li   t1, 0x4 << 1
  sw   t1, 0(t0)

  // raise interrupt threshold to max and check that the interrupt doesn't fire yet
  li   a0, 0x1
  li   t0, 0xff
  csrw MINTTHRESH, t0

  clic_enable_irq 31 0xaa

  clic_enable_irq 30 0xcc

  // wait
  li t0, 500
1:
  addi t0, t0, -1
  bnez t0, 1b

  // lower interrupt threshold (interrupt 30 should happen)
  li   a0, 30
  li   t0, 0xbb
  csrw MINTTHRESH, t0

  // wait
  li t0, 500
2:
  addi t0, t0, -1
  bnez t0, 2b

  // lower interrupt threshold (interrupt 31 should happen)
  li   a0, 31
  li   t0, 0x0
  csrw MINTTHRESH, t0

  // wait
  li t0, 500
3:
  addi t0, t0, -1
  bnez t0, 3b

  j fail_restore

pass_restore:
  csrw mtvec, s0
  li a0, 0
  ret

fail_restore:
  csrw mtvec, s0
  li a0, 1
  ret

thirty:
  // a0!=30: we should not get here, fail. else: we expect to get here, pass.
  addi a0, a0, -30
  bnez a0, fail_restore
  li a0, 0
  mret

thirtyone:
  // a0!=31: we should not get here, fail. else: we expect to get here, pass.
  addi a0, a0, -31
  bnez a0, fail_restore
  li a0, 0
  j pass_restore

  .align 8
  .global mtvt_handler
mtvt_handler:
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j thirty
  j thirtyone
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore
  j fail_restore


.align 8
.global mtvec_handler_fail
mtvec_handler_fail:
  // Restore mtvec and fail
  csrw mtvec, s0
  li a0, 1
  ret

  .data
