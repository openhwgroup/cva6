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

static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

int main(void) {
  uint32_t tmpint;
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
  tmparr[0] = tmparr[1] = tmparr[2] = tmparr[3] = 0;
  __asm__ volatile("sw %0, 0x0(%1)" : : "r"(0x334455AA), "r"(tmparr[0]));
  __asm__ volatile("sw %0, 0x4(%1)" : : "r"(0x334455BB), "r"(tmparr[0]));
  __asm__ volatile("sw %0, 0x8(%1)" : : "r"(0x334455CC), "r"(tmparr[0]));
  __asm__ volatile("sw %0, 0xC(%1)" : : "r"(0x334455DD), "r"(tmparr[0]));
  __asm__ volatile("fence.i");
  __asm__ volatile("lw %0, 0x0(%1)" : "=r"(tmpint) : "r"(tmparr[0]));
  assert_or_die(tmpint, 0x334455AA, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0x4(%1)" : "=r"(tmpint) : "r"(tmparr[1]));
  assert_or_die(tmpint, 0x334455BB, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0x8(%1)" : "=r"(tmpint) : "r"(tmparr[2]));
  assert_or_die(tmpint, 0x334455CC, "error: a fence.i should not abort a sw\n");
  __asm__ volatile("lw %0, 0xC(%1)" : "=r"(tmpint) : "r"(tmparr[3]));
  assert_or_die(tmpint, 0x334455DD, "error: a fence.i should not abort a sw\n");

  printf("Check interdigitated stores\n");
  tmparr[0] = tmparr[1] = tmparr[2] = tmparr[3] = 0;
  //TODO:ropeders

  printf("Check self-modifying code\n");
  //TODO:ropeders

  printf("Check externally modified code\n");
  //TODO:ropeders

  return EXIT_SUCCESS;
}
