// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Nils Wistoff <nwistoff@iis.ee.ethz.ch>
//
// Basic CLIC test. Based on https://github.com/pulp-platform/safety_island/blob/main/sw/tests/runtime_clic_basic/clic-basic.c

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

.align
.option norvc
.global main
main:
  // Enable interrupts (set mstatus.mie)
  csrsi mstatus, 0x8

  // Activate CLIC mode
  la t0, mtvec_handler_fail
  ori t0, t0, 0x3
  csrrw s0, mtvec, t0

  // Write mtvt base
  la t0, mtvt_handler
  csrw 0x307, t0 // mtvt

  // Set shv of irq 31
  li   t0, CLIC_CLICINT_REG(31)
  li   t1, 1 << CLIC_CLICINT_ATTR_SHV_OFFSET
  sw   t1, 0(t0)

  // set trigger type to edge-triggered
  li   t0, CLIC_CLICINT_REG(31)
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_ATTR_TRIG_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // enable irq31 via SW by writing to clicintip31
  li   t0, CLIC_CLICINT_REG(31)
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_IP_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // set number of bits for level encoding
  li   t0, CLIC_CLICCFG_REG
  li   t1, 0x4 << 1
  sw   t1, 0(t0)

  // set interrupt level and priority for interrupt 31
  li   t0, CLIC_CLICINT_REG(31)
  lw   t1, 0(t0)
  li   t2, 0xaa << CLIC_CLICINT_CTL_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // raise interrupt threshold to max and check that the interrupt doesn't fire yet
  li   a0, 0x1
  li   t0, 0xff
  csrw 0x347, t0 // mintthresh
  li   t0, CLIC_CLICINT_REG(31)
  lw   t1, 0(t0)
  li   t2, 1 << CLIC_CLICINT_IE_OFFSET
  or   t1, t1, t2
  sw   t1, 0(t0)

  // wait
  li t0, 500
1:
  addi t0, t0, -1
  bnez t0, 1b

  // lower interrupt threshold (interrupt should happen)
  li   a0, 0x0
  li   t0, 0x0
  csrw 0x347, t0 // mintthresh

  // wait
  li t0, 500
2:
  addi t0, t0, -1
  bnez t0, 2b

  j fail_restore

pass_restore:
  csrw mtvec, s0
  li a0, 0
  ret

fail_restore:
  csrw mtvec, s0
  li a0, 1
  ret

thirtyone:
  // a0=0: we should not get here, fail. else: we expect to get here, pass.
  beqz a0, pass_restore
  j fail_restore

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
  j fail_restore
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
