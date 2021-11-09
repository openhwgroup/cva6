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

#define VP_ENAB_ADDR (CV_VP_FENCEI_TAMPER_BASE + 0)
#define VP_ADDR_ADDR (CV_VP_FENCEI_TAMPER_BASE + 4)
#define VP_DATA_ADDR (CV_VP_FENCEI_TAMPER_BASE + 8)

static volatile uint32_t *vp_enab_ptr = (void *)VP_ENAB_ADDR;

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
  __asm__ volatile(
    "  li %0, %2           \n"  // Load dummy instr into vp's "data"
    "  la %1, dummy_instr  \n"
    "  lw %1, 0(%1)        \n"
    "  sw %1, 0(%0)        \n"
    "  li %0, %3           \n"  // Load exec address into vp's "addr"
    "  la %1, exec_instr   \n"
    "  sw %1, 0(%0)        \n"
    "  li %0, %4           \n"  // Enable vp
    "  li %1, 1            \n"
    "  sw %1, 0(%0)        \n"
    "dummy_instr:          \n"  // ...
    "  addi %0, x0, 222    \n"
    "  fence.i             \n"  // (Upon this fencei, vp should swap out exec_instr)
    "exec_instr:           \n"
    "  addi %0, x0, 111    \n"  // (Should execute dummy_instr instead)
    : "=r"(reg0), "=r"(reg1)
    : "i"(VP_DATA_ADDR), "i"(VP_ADDR_ADDR), "i"(VP_ENAB_ADDR));
  assert_or_die(reg0, 222, "env should have swapped the exec instruction\n");
  *vp_enab_ptr = 0;  // Disable vp

  return EXIT_SUCCESS;
}
