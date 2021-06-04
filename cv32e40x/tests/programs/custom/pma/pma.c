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
#define  NOEXEC_ADDR  0x10000  // must match pma config to cause exec fault
#define  MTVAL_READ  0

static volatile int mcause;
static volatile int mepc;
static volatile int mtval;

static void (*pma_fault_function)(void) = (void (*)(void))NOEXEC_ADDR;

void u_sw_irq_handler(void) {  // overrides a "weak" symbol in the bsp
  __asm__ volatile("csrr %0, mcause" : "=r"(mcause));
  __asm__ volatile("csrr %0, mepc" : "=r"(mepc));
  __asm__ volatile("csrr %0, mtval" : "=r"(mtval));

  if (mcause == EXCEPTION_INSN_ACCESS_FAULT) {
    printf("in exception handler for instruction access fault\n");
    return;  // should continue test, assuming no intermediary ABI function call
  } else {
    printf("error: unexpected mcause value\n");
    while (1)
      ;
  }
}

void reset_volatiles(void) {
  mcause = -1;
  mepc = -1;
  mtval = -1;
}

int main(void) {
  printf("\nHello, PMA test!\n\n");

  reset_volatiles();
  pma_fault_function();
  if (mcause != EXCEPTION_INSN_ACCESS_FAULT) {
    printf("error: expected instruction access fault\n");
    return EXIT_FAILURE;
  }
  if (mepc != NOEXEC_ADDR) {
    printf("error: expected different mepc\n");
    return EXIT_FAILURE;
  }
  if (mtval != MTVAL_READ) {
    printf("error: expected different mtval\n");
    return EXIT_FAILURE;
  }

  printf("\nGoodbye, PMA test!\n\n");
  return EXIT_SUCCESS;
}
