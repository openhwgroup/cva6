// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0

#include <stdio.h>
#include <stdlib.h>

#define  EXCEPTION_INSN_ACCESS_FAULT  1
#define  EXCEPTION_LOAD_ACCESS_FAULT  5
#define  EXCEPTION_STOREAMO_ACCESS_FAULT  7
#define  MEM_ADDR_0  0
#define  IO_ADDR  (0x1A110800 + 16)
#define  MEM_ADDR_1  0x1A111000
#define  MTVAL_READ  0
#define  MTBLJALVEC  0  // TODO update when RTL is implemented
#define  TBLJ_TARGET_ADDR  (IO_ADDR + 8)

static volatile uint32_t mcause = 0;
static volatile uint32_t mepc = 0;
static volatile uint32_t mtval = 0;

static void (*cause_instr_access_fault)(void) = (void (*)(void))IO_ADDR;

static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

void u_sw_irq_handler(void) {  // overrides a "weak" symbol in the bsp
  __asm__ volatile("csrr %0, mcause" : "=r"(mcause));
  __asm__ volatile("csrr %0, mepc" : "=r"(mepc));
  __asm__ volatile("csrr %0, mtval" : "=r"(mtval));

  //printf("exec in u_sw_irq_handler\n");
  assert_or_die(mcause, EXCEPTION_INSN_ACCESS_FAULT, "error: handler, unexpected mcause value\n");

  return;  // should continue test, assuming no intermediary ABI function call
  // TODO ensure it works for the non-function-call expected faults too  (or turn them into function calls)
}

static void reset_volatiles(void) {
  mcause = -1;
  mepc = -1;
  mtval = -1;
}

static void check_load_vs_regfile(void) {
  // within this scope, t0 regs etc should be free to use (ABI, not preserved)
  uint32_t tmp;

  // check misaligned in IO
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xAAAAAAAA), "r"(IO_ADDR));
  __asm__ volatile("sw %0, 4(%1)" : : "r"(0xBBBBBBBB), "r"(IO_ADDR));
  __asm__ volatile("li t0, 0x11223344");
  __asm__ volatile("lw t0, 3(%0)" : : "r"(IO_ADDR));
  __asm__ volatile("mv %0, t0" : "=r"(tmp));
  /* TODO enable when RTL is implemented
  assert_or_die(tmp, 0x11223344, "error: misaligned IO load shouldn't touch regfile\n");
  */

  // check misaligned border from IO to MEM
  __asm__ volatile("sw %0, -4(%1)" : : "r"(0xAAAAAAAA), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xBBBBBBBB), "r"(MEM_ADDR_1));
  __asm__ volatile("li t0, 0x22334455");
  __asm__ volatile("lw t0, 0(%0)" : : "r"(MEM_ADDR_1 - 3));
  __asm__ volatile("mv %0, t0" : "=r"(tmp));
  /* TODO enable when RTL is implemented
  assert_or_die(tmp, 0x22334455, "error: misaligned IO/MEM load shouldn't touch regfile\n");
  */

  // check misaligned border from MEM to IO
  __asm__ volatile("sw %0, -4(%1)" : : "r"(0xAAAAAAAA), "r"(IO_ADDR));
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xBBBBBBBB), "r"(IO_ADDR));
  __asm__ volatile("li t0, 0x33445566");
  __asm__ volatile("lw t0, 0(%0)" : : "r"(IO_ADDR - 1));
  __asm__ volatile("mv %0, t0" : "=r"(tmp));
  /* TODO enable when RTL is implemented
  assert_or_die(tmp, 0x33445566, "error: misaligned MEM/IO load shouldn't touch regfile\n");
  */

  // TODO can one programmatically confirm that these addresses are indeed in such regions as intended?
}

static void check_zce_push(void) {
  uint32_t defaults[] = {0xAAAAAAAA, 0xBBBBBBBB, 0xCCCCCCCC, 0xDDDDDDDD};
  uint32_t sp;
  uint32_t ra;
  uint32_t tmp;

  // Prologue
  __asm__ volatile("mv %0, sp" : "=r"(sp));  // Saving "sp", for we shall tamper with it

  // Setup preparations
  __asm__ volatile("mv sp, %0" : : "r"(MEM_ADDR_1 + 4));  // Set "sp" to have room for 1 MEM before entering IO
  __asm__ volatile("mv %0, ra" : "=r"(ra));  // Saving "ra" for later use
  __asm__ volatile("sw %0, 0(%1)" : : "r"(defaults[0]), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, -4(%1)" : : "r"(defaults[1]), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, -8(%1)" : : "r"(defaults[2]), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, -12(%1)" : : "r"(defaults[3]), "r"(MEM_ADDR_1));

  // Run the push stimuli
  /* TODO enabled when RTL is implemented
  __asm__ volatile(".word 0x000240AB");  // TODO "push {ra, s0-s1}, -16"
  */

  // Epilogue
  __asm__ volatile("mv sp, %0" : : "r"(sp));  // Better restore this quickly

  // Assert results
  /* TODO enabled when RTL is implemented
  assert_or_die(mcause, EXCEPTION_STOREAMO_ACCESS_FAULT, "error: bad push should except\n");
  assert_or_die(mepc, (MEM_ADDR_1 - 4), "error: bad push, unexpected mepc\n");
  assert_or_die(mtval, MTVAL_READ, "error: bad push, unexpected mtval\n");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  assert_or_die(tmp, ra, "error: PUSH to MEM should SW successfully\n");
  */
  __asm__ volatile("lw %0, -4(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  assert_or_die(tmp, defaults[1], "error: PUSH to IO should not SW\n");
  __asm__ volatile("lw %0, -8(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  assert_or_die(tmp, defaults[2], "error: Trailing PUSHes to IO should not SW\n");
}

static void check_zce_pop(void) {
  uint32_t defaults[] = {0xAAAAAAAA, 0xBBBBBBBB, 0xCCCCCCCC, 0xDDDDDDDD};
  register uint32_t sp asm ("s8");  // (ask C to not use the registers needed for testing)
  register uint32_t s0 asm ("s9");
  register uint32_t s1 asm ("s10");
  register uint32_t ra asm ("s11");  // Hereby pledge to not intentionally use s11, to prevent ra getting corrupted
  uint32_t tmp;

  // Prologue
  __asm__ volatile("mv %0, sp" : "=r"(sp));  // Saving "sp", for we shall tamper with it
  __asm__ volatile("mv %0, ra" : "=r"(ra));  // Saving "ra", for we shall tamper with it

  // Setup
  __asm__ volatile("mv sp, %0" : : "r"(MEM_ADDR_1 + 4 - 16));  // Set previous "sp" to have room for 1 MEM before entering IO
  __asm__ volatile("sw %0, 0(%1)" : : "r"(defaults[0]), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, -4(%1)" : : "r"(defaults[1]), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, -8(%1)" : : "r"(defaults[2]), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, -12(%1)" : : "r"(defaults[3]), "r"(MEM_ADDR_1));
  __asm__ volatile("mv %0, s0" : "=r"(s0));  // Will check against this later
  __asm__ volatile("mv %0, s1" : "=r"(s1));  // Will check against this later

  // Run the instruction
  /* TODO enable when RTL is implemented
  __asm__ volatile("pop {ra, s0-s1}, 16");
  */

  // Epilogue 1/2
  __asm__ volatile("mv sp, %0" : : "r"(sp));

  // Assert results
  /* TODO enable when RTL is implemented
  assert_or_die(mcause, EXCEPTION_LOAD_ACCESS_FAULT, "error: bad pop should except\n");
  assert_or_die(mepc, (MEM_ADDR_1 - 4), "error: bad pop, unexpected mepc\n");
  assert_or_die(mtval, MTVAL_READ, "error: bad pop, unexpected mtval\n");
  __asm__ volatile("mv %0, ra" : "=r"(tmp));
  assert_or_die(tmp, defaults[0], "error: POP from MEM should LW ra successfully\n");
  */
  __asm__ volatile("mv %0, s0" : "=r"(tmp));
  assert_or_die(tmp, s0, "error: POP from IO should not LW\n");
  __asm__ volatile("mv %0, s1" : "=r"(tmp));
  assert_or_die(tmp, s1, "error: POP from IO should not continue LWing\n");
  //TODO are assertions good enough that C accidentally using the same registers will either be caught or not be a problem?

  // Epilogue 2/2
  __asm__ volatile("mv ra, %0" : : "r"(ra));
}

static int fail_first_tblj(void) {
  int mepc = -1;

  /* TODO enable when RTL is implemented
  // TODO make sure the target address is non-executable, so we can check if mtval matches first fetch
  __asm__ volatile("c.tbljal 0");
  */
  __asm__ volatile("auipc %0, 0" : "=r"(mepc));
  mepc -= 4;

  return mepc;
}

int main(void) {
  uint32_t tmp;

  printf("\nHello, PMA test!\n\n");
  assert_or_die(mcause, 0, "error: mcause variable should initially be 0\n");
  assert_or_die(mepc, 0, "error: mepc variable should initially be 0\n");
  assert_or_die(mtval, 0, "error: mtval variable should initially be 0\n");

  // TODO "mtval" should in the future not be read-only read-zero.


  // Exec should only work for "main memory" regions

  reset_volatiles();
  cause_instr_access_fault();
  assert_or_die(mcause, EXCEPTION_INSN_ACCESS_FAULT, "error: expected instruction access fault\n");
  assert_or_die(mepc, IO_ADDR, "error: expected different mepc\n");
  assert_or_die(mtval, MTVAL_READ, "error: expected different mtval\n");


  // Non-naturally aligned stores to I/O regions

  // sanity check that aligned stores are ok
  reset_volatiles();
  tmp = 0xAAAAAAAA;
  __asm__ volatile("sw %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(mcause, -1, "error: aligned store should not change mcause\n");
  assert_or_die(mepc, -1, "error: aligned store should not change mepc\n");
  assert_or_die(mtval, -1, "error: aligned store should not change mtval\n");

  // check that misaligned stores except
  /* TODO enable when RTL is implemented
  reset_volatiles();
  tmp = 0xBBBBBBBB;
  __asm__ volatile("sw %0, 1(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(mcause, EXCEPTION_STOREAMO_ACCESS_FAULT, "error: misaligned store unexpected mcause\n");
  assert_or_die(mepc, (IO_ADDR + 1), "error: misaligned store unexpected mepc\n");
  assert_or_die(mtval, MTVAL_READ, "error: misaligned store unexpected mtval\n");
  */

  // check that misaligned store to MEM is alright
  reset_volatiles();
  tmp = 0xCCCCCCCC;
  __asm__ volatile("sw %0, -9(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(mcause, -1, "error: misaligned store to main affected mcause\n");
  assert_or_die(mepc, -1, "error: misaligned store to main affected mepc\n");
  assert_or_die(mtval, -1, "error: misaligned store to main affected mtval\n");


  // Non-naturally aligned loads within I/O regions

  // sanity check that aligned load is no problem
  reset_volatiles();
  tmp = 0;
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));  // Depends on "store" test filling memory first
  assert_or_die(!tmp, 0, "error: load should not yield zero\n");  // TODO ensure memory content matches
  assert_or_die(mcause, -1, "error: natty access should not change mcause\n");
  assert_or_die(mepc, -1, "error: natty access should not change mepc\n");
  assert_or_die(mtval, -1, "error: natty access should not change mtval\n");

  // check that misaligned load will except
  /* TODO enable when RTL is implemented
  reset_volatiles();
  __asm__ volatile("lw %0, 5(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(mcause, EXCEPTION_LOAD_ACCESS_FAULT, "error: misaligned IO load should except\n");
  assert_or_die(mepc, (IO_ADDR + 5), "error: misaligned IO load unexpected mepc\n");
  assert_or_die(mtval, MTVAL_READ, "error: misaligned IO load unexpected mtval\n");
  */
  // TODO more kinds of |addr[0:1]? Try LH too?

  // check that misaligned to MEM does not fail
  reset_volatiles();
  tmp = 0;
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(0x80));
  assert_or_die(!tmp, 0, "error: load from main should not yield zero\n");
  assert_or_die(mcause, -1, "error: main access should not change mcause\n");
  assert_or_die(mepc, -1, "error: main access should not change mepc\n");
  assert_or_die(mtval, -1, "error: main access should not change mtval\n");


  // Misaligned load fault shouldn't touch regfile

  // check that various split load access fault leaves regfile untouched
  check_load_vs_regfile();


  // Misaligned store fault shouldn't reach bus in second access

  // check IO store failing in first access
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xAAAAAAAA), "r"(IO_ADDR));
  __asm__ volatile("sw %0, 4(%1)" : : "r"(0xBBBBBBBB), "r"(IO_ADDR));
  __asm__ volatile("sw %0, 2(%1)" : : "r"(0x11223344), "r"(IO_ADDR));
  /* TODO enable when RTL is implemented
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(tmp, 0xAAAAAAAA, "error: misaligned first store entered bus\n");
  __asm__ volatile("lw %0, 4(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(tmp, 0xBBBBBBBB, "error: misaligned second store entered bus\n");
  */
  // TODO how to programmatically confirm that these region settings match as intended?

  // check IO to MEM store failing in first access
  __asm__ volatile("sw %0, -4(%1)" : : "r"(0xAAAAAAAA), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xBBBBBBBB), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, -2(%1)" : : "r"(0x22334455), "r"(MEM_ADDR_1));
  /* TODO enable when RTL is implemented
  __asm__ volatile("lw %0, -4(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  assert_or_die(tmp, 0xAAAAAAAA, "error: misaligned IO/MEM first store entered bus\n");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  assert_or_die(tmp, 0xBBBBBBBB, "error: misaligned IO/MEM second store entered bus\n");
  */
  // TODO how to programmatically confirm that these region settings match as intended?


  // Atomics should work only where it is allowed

  // Sanity check that atomic ops (lr/sc) to allowed regions is ok
  reset_volatiles();
  /* TODO enable when RTL is implemented
  __asm__ volatile("lr.w %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  __asm__ volatile("sc.w %0, %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  */
  assert_or_die(mcause, -1, "error: atomics to legal region should not except\n");
  assert_or_die(mepc, -1, "error: atomics to legal region unexpected mepc\n");
  assert_or_die(mtval, -1, "error: atomics to legal region unexpected mtval\n");

  // Load-reserved to disallowed regions raises precise exception
  reset_volatiles();
  /* TODO enable when RTL is implemented
  __asm__ volatile("lr.w %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(mcause, EXCEPTION_LOAD_ACCESS_FAULT, "error: load-reserved to non-atomic should except\n");
  assert_or_die(mepc, IO_ADDR, "error: load-reserved to non-atomic unexpected mepc\n");
  assert_or_die(mtval, MTVAL_READ, "error: load-reserved to non-atomic unexpected mtval\n");
  */

  // Store-conditional to disallowed regions raises precise exception
  reset_volatiles();
  /* TODO enable when RTL is implemented
  __asm__ volatile("sc.w %0, %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(mcause, EXCEPTION_STOREAMO_ACCESS_FAULT, "error: store-conditional to non-atomic should except\n");
  assert_or_die(mepc, IO_ADDR, "error: store-conditional to non-atomic unexpected mepc\n");
  assert_or_die(mtval, MTVAL_READ, "error: store-conditional to non-atomic unexpected mtval\n");
  */


  // Check Zce-related PMA features

  // Push instrs should fault to IO but pass for MEM
  check_zce_push();

  // Pop instrs should fault to IO but pass for MEM
  check_zce_pop();

  // Table jump failing first fetch should be the fault of the table jump
  reset_volatiles();
  tmp = fail_first_tblj();
  /* TODO enable when RTL is implemented
  assert_or_die(mcause, EXCEPTION_INSN_ACCESS_FAULT, "error: tblj failing first should instruction access fault\n");
  assert_or_die(mepc, tmp, "error: tblj first expected different mepc\n");
  assert_or_die(mtval, MTBLJALVEC, "error: tblj first expected different mtval\n");
  */

  // Table jump failing second fetch should be the fault of the target
  reset_volatiles();
  /* TODO enable when RTL is implemented
  make sure table is executable but target is not
  __asm__ volatile("c.tbljal 1");
  assert_or_die(mcause, EXCEPTION_INSN_ACCESS_FAULT, "error: tblj failing second should instruction access fault\n");
  assert_or_die(mepc, TBLJ_TARGET_ADDR, "error: tblj second expected different mepc\n");
  assert_or_die(mtval, MTVAL_READ, "error: tblj second expected different mtval\n");
  */


  printf("\nGoodbye, PMA test!\n\n");
  return EXIT_SUCCESS;
}
