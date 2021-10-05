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

#define TEST_LOOPS 6

// Virtual peripheral registers for manipulating the OBI-I error response generation
#define ERR_ADDR_MIN   ((volatile uint32_t *) 0x15001080)
#define ERR_ADDR_MAX   ((volatile uint32_t *) 0x15001084)
#define ERR_VALID      ((volatile uint32_t *) 0x15001088)

// Globals
volatile uint32_t  bus_fault_count     = 0;
volatile uint32_t  bus_fault_count_exp = 3;

// Special handler for instruction bus faults
void handle_insn_bus_fault(void) {
  if (++bus_fault_count == bus_fault_count_exp) {
    *(ERR_VALID + 6*0) = 0;

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

__attribute__((aligned(4)))
void bus_error_prefetch_func() {
  asm volatile("c.addi x0,0");
  asm volatile("c.addi x0,0");
  asm volatile("c.addi x0,0");
  asm volatile("c.addi x0,0");
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
  *(ERR_ADDR_MIN + 6*0) = (uint32_t) bus_error_func_word_align;
  *(ERR_ADDR_MAX + 6*0) = (uint32_t) bus_error_func_word_align;
  *(ERR_VALID + 6*0)    = 1;
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
  *(ERR_ADDR_MIN + 6*0) = (uint32_t) bus_error_func_halfword_align;
  *(ERR_ADDR_MAX + 6*0) = (uint32_t) bus_error_func_halfword_align;
  *(ERR_VALID + 6*0)    = 1;
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

  *(ERR_ADDR_MIN + 6*0) = ((uint32_t) bus_error_prefetch_func) + 4 * 2 + 4;
  *(ERR_ADDR_MAX + 6*0) = ((uint32_t) bus_error_prefetch_func) + 4 * 2 + 4;
  *(ERR_VALID + 6*0)    = 1;

  bus_fault_count_exp = 1;
  bus_error_prefetch_func();

  if (bus_fault_count != 0) {
    printf("test_prefetch_i_error(): Received instruction bus faults on a prefetched but not executed instruction\n");

    return EXIT_FAILURE;
  }

  *(ERR_VALID + 6*0)    = 0;

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

