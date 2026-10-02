/* RVMODEL macros for the cva6tb standalone testbench.
 * SPDX-License-Identifier: Apache-2.0
 *
 * Two DUT specific mechanisms are needed and both are testbench registers
 * rather than a front-end server, so there is no tohost here:
 *
 *   EOC     0x1000_0004  bit 0 ends the simulation, bits 31:1 are the return
 *                        code. Writing 1 is "done, code 0" -- a pass; writing 3
 *                        is "done, code 1" -- a failure. See cva6tb_regs.sv.
 *   console 0x1000_1000  byte writes, flushed to stdout on a newline.
 *                        See cva6tb_sim_console.sv.
 */

#ifndef _RVMODEL_MACROS_H
#define _RVMODEL_MACROS_H

/* Must be defined, and is empty here: a test ends through the EOC register,
 * never tohost. For the reference run on Sail, ACT's own sail_macros.h replaces
 * this and the halt macros below with its tohost versions. */
#define RVMODEL_DATA_SECTION

/* CVA6 implements a conforming M-mode, so the test environment may use its own
 * boot and trap handling. Without this the per-mode trap save areas are never
 * emitted and any test that takes a trap fails to link on Mtramptbl_sv. */
#define STANDARD_SM_SUPPORTED

##### TERMINATION #####

#define RVMODEL_HALT_PASS   \
  li t0, 0x10000004        ;\
  li t1, 1                 ;\
  sw t1, 0(t0)             ;\
self_loop_pass:            ;\
  j self_loop_pass         ;\

#define RVMODEL_HALT_FAIL   \
  li t0, 0x10000004        ;\
  li t1, 3                 ;\
  sw t1, 0(t0)             ;\
self_loop_fail:            ;\
  j self_loop_fail         ;\

##### IO #####

#define RVMODEL_IO_WRITE_STR(_R1, _R2, _R3, _STR_PTR) \
1:                           ;                        \
  lbu  _R1, 0(_STR_PTR)      ; /* Load byte */         \
  beqz _R1, 3f               ; /* Exit if null */      \
2:                           ;                         \
  li   _R2, 0x10001000       ; /* sim console */       \
  sw   _R1, 0(_R2)           ;                         \
  addi _STR_PTR, _STR_PTR, 1 ; /* Next char */         \
  j 1b                       ;                         \
3:

##### Machine timer #####

/* The time CSR is not implemented in the core, so the test environment reads
 * mtime from the CLINT instead: base 0x0204_0000 (cva6tb_pkg.sv) plus the
 * clint register block's 0xbff8 mtime offset. */
#define RVMODEL_MTIME_ADDRESS 0x0204BFF8
/* mtimecmp for hart 0, at the clint block's 0x4000 offset. */
#define RVMODEL_MTIMECMP_ADDRESS 0x02044000
/* msip for hart 0, at the clint block's 0x0 offset. */
#define RVMODEL_MSIP_ADDRESS 0x02040000

##### Interrupts #####

/* mtime counts the testbench's 1 MHz RTC (cva6tb_test_simple.sv), a tick
 * every 1000 cycles of the 1 GHz core clock. */
#define RVMODEL_MAX_CYCLES_PER_TIMER_TICK 1000
/* In ticks: covers the round trip through the machine-mode handler that a
 * test running below machine mode makes to arm the timer, about 1000
 * instructions, several times over. */
#define RVMODEL_TIMER_INT_SOON_DELAY 10
/* Polls of mip after clearing a source: a write to the CLINT crosses the AXI
 * crossbar and the register bus before mip follows it. The loop stops as
 * soon as the bit clears. */
#define RVMODEL_INTERRUPT_LATENCY 100

/* The external interrupt lines: the testbench ORs bits 0 (M-mode) and 1
 * (S-mode) of the platform control register at 0x1000_0008 into the core's
 * external interrupt inputs (cva6tb_regs.sv), a level the macros raise and
 * lower directly, like the interrupt generator ACT gives Sail. The S-mode line
 * is distinct from the software-writable mip.SEIP. Both lines share the
 * register, so each macro changes only its own bit. The supervisor software
 * and timer interrupts need no macros: ACT raises them by writing mip. */
#define RVMODEL_EXT_INT_ADDRESS 0x10000008

#define RVMODEL_SET_MEXT_INT(_R1, _R2)  \
  li   _R2, RVMODEL_EXT_INT_ADDRESS    ;\
  lw   _R1, 0(_R2)                     ;\
  ori  _R1, _R1, 1                     ;\
  sw   _R1, 0(_R2)                     ;

#define RVMODEL_CLR_MEXT_INT(_R1, _R2)  \
  li   _R2, RVMODEL_EXT_INT_ADDRESS    ;\
  lw   _R1, 0(_R2)                     ;\
  andi _R1, _R1, ~1                    ;\
  sw   _R1, 0(_R2)                     ;

#define RVMODEL_SET_SEXT_INT(_R1, _R2)  \
  li   _R2, RVMODEL_EXT_INT_ADDRESS    ;\
  lw   _R1, 0(_R2)                     ;\
  ori  _R1, _R1, 2                     ;\
  sw   _R1, 0(_R2)                     ;

#define RVMODEL_CLR_SEXT_INT(_R1, _R2)  \
  li   _R2, RVMODEL_EXT_INT_ADDRESS    ;\
  lw   _R1, 0(_R2)                     ;\
  andi _R1, _R1, ~2                    ;\
  sw   _R1, 0(_R2)                     ;

#endif // _RVMODEL_MACROS_H
