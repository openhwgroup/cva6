/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
**
** Basic turnon test for instruction bus faults (errors on OBI-I fetch)
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include "corev_uvmt.h"

#define TEST_LOOPS 6

// Globals
volatile uint32_t  bus_fault_count     = 0;
volatile uint32_t  bus_fault_count_exp = 3;

// Special handler for instruction bus faults
void handle_insn_bus_fault(void) {
  if (++bus_fault_count == bus_fault_count_exp) {
    *CV_VP_OBI_SLV_RESP_I_ERR_VALID = 0;

    asm volatile("fence");
  }

  asm volatile("j end_handler_ret");
}

// Test function where first "word-aligned" instruction will be tested
__attribute__((aligned(4)))
void bus_error_func_word_align() {
  printf("In the word-aligned bus error func\n");
}

// Test function where first "word-aligned" instruction will be tested
__attribute__((aligned(4)))
void bus_error_func_halfword_align() {
  asm volatile("c.addi x0,0");
  asm volatile("c.addi x0,0");
  printf("In the halfword-aligned bus error func\n");
}

// This is a dummy function to exercise bus errors in the prefetcher to ensure they do not
// propagate to faults.  The caller of this function should setup a bus error to occur 4 instructions
// beyond the end of this function.  OBI should see the error but the caller should ensure no
// bus faults are seen (via the handler counter)
__attribute__((aligned(4)))
void bus_error_prefetch_func() {
  asm volatile("addi x0,x20,0");
  asm volatile("addi x0,x20,0");
  asm volatile("addi x0,x20,0");
}

int test_word_aligned_i_error() {
  // Call initially without error injection
  bus_error_func_word_align();

  if (bus_fault_count != 0) {
    printf("test_word_aligned_i_error(): Received instruction bus faults before injecting\n");
    return EXIT_FAILURE;
  }

  // Inject errors via OBI VP and call function
  bus_fault_count_exp = 4;
  *CV_VP_OBI_SLV_RESP_I_ERR_ADDR_MIN = (uint32_t) bus_error_func_word_align;
  *CV_VP_OBI_SLV_RESP_I_ERR_ADDR_MAX = (uint32_t) bus_error_func_word_align;
  *CV_VP_OBI_SLV_RESP_I_ERR_VALID    = 1;
  asm volatile("fence");

  bus_error_func_word_align();

  // Verify we received number of faults
  if (bus_fault_count != bus_fault_count_exp) {
    printf("test_word_aligned_i_error(): Only recevied %lu bus faults, expected %lu\n", bus_fault_count, bus_fault_count_exp);
    return EXIT_FAILURE;
  }

  bus_fault_count = 0;

  return EXIT_SUCCESS;
}

int test_halfword_aligned_i_error() {
  // Create a new function pointer to point to 1 compressed instruction after
  // start of bus_error_func_halfword_align()
  void (*bus_error_func_halfword_align_p2)(void) = ((uint32_t) bus_error_func_halfword_align) + 2;

  // Call initially without error injection
  (*bus_error_func_halfword_align_p2)();

  if (bus_fault_count != 0) {
    printf("test_halfword_aligned_i_error(): Received instruction bus faults before injecting\n");
    return EXIT_FAILURE;
  }

  // Inject errors via OBI VP and call function
  bus_fault_count_exp = 5;
  *CV_VP_OBI_SLV_RESP_I_ERR_ADDR_MIN = (uint32_t) bus_error_func_halfword_align;
  *CV_VP_OBI_SLV_RESP_I_ERR_ADDR_MAX = (uint32_t) bus_error_func_halfword_align;
  *CV_VP_OBI_SLV_RESP_I_ERR_VALID    = 1;
  asm volatile("fence");

  (*bus_error_func_halfword_align_p2)();

  // Verify we received number of faults
  if (bus_fault_count != bus_fault_count_exp) {
    printf("test_halfword_aligned_i_error(): Only recevied %lu bus faults, expected %lu\n", bus_fault_count, bus_fault_count_exp);
    return EXIT_FAILURE;
  }

  bus_fault_count = 0;

  return EXIT_SUCCESS;
}

int test_prefetch_i_error() {

  if (bus_fault_count != 0) {
    printf("test_prefetch_i_error(): Received instruction bus faults before injecting\n");

    return EXIT_FAILURE;
  }

  // Seed an OBI I error one instruciton past the end of bus_error_prefetch_func (it should contain 4 32-bit instructions)
  *CV_VP_OBI_SLV_RESP_I_ERR_ADDR_MIN = ((uint32_t) bus_error_prefetch_func) + 4 * 4;
  *CV_VP_OBI_SLV_RESP_I_ERR_ADDR_MAX = ((uint32_t) bus_error_prefetch_func) + 4 * 4;
  *CV_VP_OBI_SLV_RESP_I_ERR_VALID    = 1;

  bus_fault_count_exp = 1;
  bus_error_prefetch_func();

  if (bus_fault_count != 0) {
    printf("test_prefetch_i_error(): Received instruction bus faults on a prefetched but not executed instruction\n");

    return EXIT_FAILURE;
  }

  *CV_VP_OBI_SLV_RESP_I_ERR_VALID = 0;

  return EXIT_SUCCESS;
}

int main(int argc, char *argv[]) {
  printf("Start instr_bus_error test\n");

  for (int i = 0; i < TEST_LOOPS; i++) {
    if (test_word_aligned_i_error() != EXIT_SUCCESS) {
      return EXIT_FAILURE;
    }

    if (test_halfword_aligned_i_error() != EXIT_SUCCESS) {
      return EXIT_FAILURE;
    }

    if (test_prefetch_i_error() != EXIT_SUCCESS) {
      return EXIT_FAILURE;
    }
  }

  return EXIT_SUCCESS;
}


