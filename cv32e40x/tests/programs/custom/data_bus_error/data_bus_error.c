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
#include <stdint.h>
#include <stdlib.h>

#define TEST_LOOPS 6

// Virtual peripheral registers for manipulating the OBI-I error response generation
#define ERR_ADDR_MIN   ((volatile uint32_t *) 0x15001080)
#define ERR_ADDR_MAX   ((volatile uint32_t *) 0x15001084)
#define ERR_VALID      ((volatile uint32_t *) 0x15001088)

// Globals
volatile uint32_t  load_bus_fault_count      = 0;
volatile uint32_t  load_bus_fault_exp        = 0;
volatile uint32_t  store_bus_fault_count     = 0;
volatile uint32_t  store_bus_fault_exp       = 0;
volatile uint32_t  error_word                = 0xbeef1234;

void handle_data_load_bus_fault() {
  load_bus_fault_count++;
}

void handle_data_store_bus_fault() {
  store_bus_fault_count++;
}

int test_data_load_error() {
  volatile uint32_t data_word;

  printf("Testing data load bus fault injection\n");

  load_bus_fault_exp  = 0;
  store_bus_fault_exp = 0;

  if (load_bus_fault_count != 0) {
    printf("test_data_load_error: Received load bus faults before injecting");
    return EXIT_FAILURE;
  }

  if (store_bus_fault_count != 0) {
    printf("test_data_store_error: Received load bus faults before injecting");
    return EXIT_FAILURE;
  }

  // Write the Virtual Peripheral
  *(ERR_ADDR_MIN + 6*1) = (uint32_t) &error_word;
  *(ERR_ADDR_MAX + 6*1) = (uint32_t) &error_word;
  *(ERR_VALID + 6*1)    = 1;
  asm volatile("fence");

  // Do the load
  data_word = error_word;

  // Verify we received a fault
  if (load_bus_fault_count != load_bus_fault_exp) {
    printf("loads: recevied %lu bus faults, expected %lu\n", load_bus_fault_count, load_bus_fault_exp);
    return EXIT_FAILURE;
  }
  if (store_bus_fault_count != store_bus_fault_exp) {
    printf("loads: recevied %lu bus faults, expected %lu\n", store_bus_fault_count, store_bus_fault_exp);
    return EXIT_FAILURE;
  }

  load_bus_fault_count = 0;
  store_bus_fault_count = 0;

  return EXIT_SUCCESS;
}

int test_data_store_error() {
  volatile uint32_t data_word;

  printf("Testing data store bus fault injection\n");

  load_bus_fault_exp  = 0;
  store_bus_fault_exp = 0;

  if (load_bus_fault_count != 0) {
    printf("test_data_load_error: Received load bus faults before injecting");
    return EXIT_FAILURE;
  }

  if (store_bus_fault_count != 0) {
    printf("test_data_store_error: Received load bus faults before injecting");
    return EXIT_FAILURE;
  }

  // Write the Virtual Peripheral
  *(ERR_ADDR_MIN + 6*1) = (uint32_t) &error_word;
  *(ERR_ADDR_MAX + 6*1) = (uint32_t) &error_word;
  *(ERR_VALID + 6*1)    = 1;
  asm volatile("fence");

  // Do the store
  data_word = 0x12345678;
  error_word = data_word;

  // Verify we received a fault
  if (load_bus_fault_count != load_bus_fault_exp) {
    printf("loads: recevied %lu bus faults, expected %lu\n", load_bus_fault_count, load_bus_fault_exp);
    return EXIT_FAILURE;
  }
  if (store_bus_fault_count != store_bus_fault_exp) {
    printf("loads: recevied %lu bus faults, expected %lu\n", store_bus_fault_count, store_bus_fault_exp);
    return EXIT_FAILURE;
  }

  load_bus_fault_count = 0;
  store_bus_fault_count = 0;

  return EXIT_SUCCESS;
}

int main(int argc, char *argv[])
{
  printf("Start data_bus_error test\n");

  for (int i = 0; i < TEST_LOOPS; i++) {
    if (test_data_load_error() != EXIT_SUCCESS) {
      return EXIT_FAILURE;
    }
    if (test_data_store_error() != EXIT_SUCCESS) {
      return EXIT_FAILURE;
    }
  }

  return EXIT_SUCCESS;
}
