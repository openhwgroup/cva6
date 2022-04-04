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

#define  ADDR  0x1A110800  // Repurposing the dbg section because it is otherwise not occupied in this test

void u_sw_irq_handler(void) {  // overrides a "weak" symbol in the bsp
  printf("u_sw_irq_handler: exception occured\n");
  exit(EXIT_FAILURE);
}

int main(void) {
  uint32_t tmp;

  printf("\nhello pma_0reg\n\n");


  // Misaligned should pass

  // Misaligned load should pass
  __asm__ volatile("lh %0, 7(%1)" : "=r"(tmp) : "r"(ADDR));  // would except and not continue if anything went wrong

  // Misaligned store should pass
  __asm__ volatile("sw %0, 9(%1)" : "=r"(tmp) : "r"(ADDR));


  // Atomics should pass

  // Load-reserved should pass
  /* TODO enable when RTL is implemented
  __asm__ volatile("lr.w %0, (%1)" : "=r"(tmp) : "r"(ADDR + 8));
  */

  // Store-conditional should pass
  /* TODO enable when RTL is implemented
  __asm__ volatile("sc.w %0, %0, (%1)" : "=r"(tmp) : "r"(ADDR + 12));
  */


  printf("\ngoodbye pma_0reg\n\n");
  return EXIT_SUCCESS;
}
