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
//#define  WORD_ADDR_HIGH 0x1FFFFFFF  // NB! Needs pma in vPlan's "Test configuration 3"
#define  WORD_ADDR_HIGH ((0x1A110800 + 16) >> 2)  // TODO this uses dbg addr (plus offset)
#define  ADDR_HIGH  (WORD_ADDR_HIGH << 2)
#define  IO_ADDR  ADDR_HIGH
#define  MTVAL_READ  0

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
  assert_or_die(mcause, EXCEPTION_INSN_ACCESS_FAULT, "error: unexpected mcause value\n");

  return;  // should continue test, assuming no intermediary ABI function call
}

void reset_volatiles(void) {
  mcause = -1;
  mepc = -1;
  mtval = -1;
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


  // Non-naturally aligned loads within I/O regions

  // sanity check that aligned load is no problem
  reset_volatiles();
  tmp = 0;
  __asm__ volatile("lw %0, 4(%1)" : "=r"(tmp) : "r"(IO_ADDR));
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

  // check that misaligned to MAIN does not fail
  reset_volatiles();
  tmp = 0;
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(0x80));
  assert_or_die(!tmp, 0, "error: load from main should not yield zero\n");
  assert_or_die(mcause, -1, "error: main access should not change mcause\n");
  assert_or_die(mepc, -1, "error: main access should not change mepc\n");
  assert_or_die(mtval, -1, "error: main access should not change mtval\n");


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

  // check that misaligned store to MAIN is alright
  reset_volatiles();
  tmp = 0xCCCCCCCC;
  __asm__ volatile("sw %0, -9(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(mcause, -1, "error: misaligned store to main affected mcause\n");
  assert_or_die(mepc, -1, "error: misaligned store to main affected mepc\n");
  assert_or_die(mtval, -1, "error: misaligned store to main affected mtval\n");


  printf("\nGoodbye, PMA test!\n\n");
  return EXIT_SUCCESS;
}
