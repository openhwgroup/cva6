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
#include "corev_uvmt.h"

static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

int main(void) {
  uint32_t tmpint;
  register uint32_t reg0;
  register uint32_t reg1;
  uint32_t tmparr[4];
  uint32_t *tmpptr;

  printf("fencei test\n");

  printf("Sanity check a simple store/load\n");
  tmpint = 0;
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0x11223344), "r"(tmpint));
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmpint) : "r"(tmpint));
  assert_or_die(tmpint, 0x11223344, "error: a simple sw/lw should give written value back\n");

  printf("Check store/fencei/load\n");
  tmpint = 0;
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0x22334455), "r"(tmpint));
  __asm__ volatile("fence.i");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmpint) : "r"(tmpint));
  assert_or_die(tmpint, 0x22334455, "error: a fence.i should not abort a sw\n");

  printf("Check multiple stores\n");
  tmpint = tmparr[0] = tmparr[1] = tmparr[2] = tmparr[3] = 0;
  __asm__ volatile("sw %0, 0x0(%1)" : : "r"(0x334455AA), "r"(tmparr[0]));
  __asm__ volatile("sw %0, 0x4(%1)" : : "r"(0x334455BB), "r"(tmparr[0]));
  __asm__ volatile("sw %0, 0x8(%1)" : : "r"(0x334455CC), "r"(tmparr[0]));
  __asm__ volatile("sw %0, 0xC(%1)" : : "r"(0x334455DD), "r"(tmparr[0]));
  __asm__ volatile("fence.i");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmpint) : "r"(*tmparr + 0x0));
  assert_or_die(tmpint, 0x334455AA, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmpint) : "r"(*tmparr + 0x4));
  assert_or_die(tmpint, 0x334455BB, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmpint) : "r"(*tmparr + 0x8));
  assert_or_die(tmpint, 0x334455CC, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmpint) : "r"(*tmparr + 0xC));
  assert_or_die(tmpint, 0x334455DD, "error: a fence.i should not abort a sw\n");

  printf("Check interdigitated stores\n");
  tmpint = tmparr[0] = tmparr[1] = tmparr[2] = tmparr[3] = 0;
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0x445566AA), "r"(*tmparr + 0x0));
  __asm__ volatile("fence.i");
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0x445566BB), "r"(*tmparr + 0x4));
  __asm__ volatile("fence.i");
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0x445566CC), "r"(*tmparr + 0x8));
  __asm__ volatile("fence.i");
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0x445566DD), "r"(*tmparr + 0xC));
  __asm__ volatile("fence.i");
  __asm__ volatile("lw %0, 0x0(%1)" : "=r"(tmpint) : "r"(*tmparr));
  assert_or_die(tmpint, 0x445566AA, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0x4(%1)" : "=r"(tmpint) : "r"(*tmparr));
  assert_or_die(tmpint, 0x445566BB, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0x8(%1)" : "=r"(tmpint) : "r"(*tmparr));
  assert_or_die(tmpint, 0x445566CC, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0xC(%1)" : "=r"(tmpint) : "r"(*tmparr));
  assert_or_die(tmpint, 0x445566DD, "error: a fence.i should not abort a sw\n");

  printf("Check self-modifying code\n");
  reg0 = reg1 = 0;
  __asm__ volatile(
    // Overwrite "old" instr with "new" instr
    "  la %0, new      \n"
    "  lw %0, 0(%0)    \n"
    "  la %1, old      \n"
    "  j run           \n"
    "new:              \n"
    "  addi %0, x0, 234\n"
    "  j end           \n"
    "run:              \n"
    "  sw %0, 0(%1)    \n"
    "  fence.i         \n"  // Can use "nop" instead of fence.i, to see how it otherwise fails
    "old:              \n"
    "  addi %0, x0, 123\n"
    "end:              \n"
    : "=r"(reg0), "=r"(reg1));
  assert_or_die(reg0, 234, "overwriting instruction data should be visible after fencei\n");

  printf("Check env-modifying code\n");
  tmpptr = CV_VP_FENCEI_TAMPER_BASE;  //TODO volatile global
  *tmpptr = 0;  // TODO remove
  //TODO

  return EXIT_SUCCESS;
}
