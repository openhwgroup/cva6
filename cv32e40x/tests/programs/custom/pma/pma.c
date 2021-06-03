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

// TODO should license be just Apache, or Solderpad?

#include <stdio.h>
#include <stdlib.h>

#define  EXCEPTION_INSN_ACCESS_FAULT  1

static volatile int iaf_occured = 0;

void u_sw_irq_handler(void) {  // overrides a "weak" symbol in the bsp
  unsigned int mcause = -1;

  __asm__ volatile("csrr %0, mcause" : "=r"(mcause));

  if (mcause == EXCEPTION_INSN_ACCESS_FAULT) {
    // TODO check "iaf_expected"?
    iaf_occured = 1;
    printf("in exception handler for instruction access fault\n");
    return;  // should continue test, assuming no intermediary ABI function call
  } else {
    printf("error: pma test unexpected mcause value\n");
    while (1)
      ;
  }
}

int main(void) {
  printf("\nHello, PMA test!\n\n");

  void (*pma_fault_function)(void) = (void (*)(void))0x10000;  // TODO magicnum
  iaf_occured = 0;
  pma_fault_function();
  if (!iaf_occured) {
    printf("error: pma test expected instruction access fault\n");
    return EXIT_FAILURE;
  }

  printf("\nGoodbye, PMA test!\n\n");
  return EXIT_SUCCESS;
}
