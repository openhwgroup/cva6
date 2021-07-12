/*
 * Copyright (C) 2021 ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* 
 * Mantainer: Luca Valente (luca.valente2@unibo.it)
 */

#include <stdio.h>
#include <stdint.h>
#include "utils.h"
#include "../common/encoding.h"
#define BUFFER_SIZE 32
#define ARCHI_GPIO_ADDR 0xC1002000
#define GPIO_PADDIR_0_31_OFFSET 0x0
#define GPIO_PADEN_0_31_OFFSET 0x4
#define GPIO_PADOUT_0_31_OFFSET 0xC
#define GPIO_GPIOEN_32_63_OFFSET 0x3C
#define GPIO_PADIN_32_63_OFFSET 0x40
//#define VERBOSE
//#define EXTRA_VERBOSE

#define pulp_write32(add, val_) (*(volatile unsigned int *)(long)(add) = val_)
#define pulp_read32(add) (*(volatile unsigned int *)(long)(add))
 
uint32_t invert(uint32_t a)
{
        uint32_t res         = 0;          //Result
        for ( int j=0; j<32; j++) {
          res |= ( ((a & (1<<j)) >> j ) << (31-j) );          
        }
        return res;
}

int main() {

  uint32_t error = 0;
  uint32_t address;
  uint32_t val_wr = 0x00000000;
  uint32_t val_rd = 0;
  uint32_t gpio_out;
  uint32_t gpio_in;
  uint32_t val_rd1;
  uint32_t gpio_val;

  #ifdef VERBOSE
  printf("GPIO[63-i] driven by GPIO[i] in Hardware \n");
  printf("[PRE-TEST] errors = %0d\n",error);  
  printf("Set GPIOs[31:0] as input, the remaining as output\n");
  #endif
  
  address = ARCHI_GPIO_ADDR + GPIO_PADDIR_0_31_OFFSET;
  val_wr = 0xFFFFFFFF;
  pulp_write32(address, val_wr);
  while(pulp_read32(address) != val_wr);
    
    
  #ifdef VERBOSE
  printf("Setting first 32 GPIOS outputs=1\n");
  #endif
  
  address = ARCHI_GPIO_ADDR + GPIO_PADOUT_0_31_OFFSET;
  val_wr = 0xdeadbeef;
  pulp_write32(address, val_wr);
  while(pulp_read32(address) != val_wr);

  #ifdef VERBOSE
  printf("Enable clock to allow sampling for GPIOs[63:32]\n");
  #endif
  
  address = ARCHI_GPIO_ADDR + GPIO_GPIOEN_32_63_OFFSET;
  val_wr = 0xFFFFFFFF;
  pulp_write32(address, val_wr);
  while(pulp_read32(address) != val_wr);

  #ifdef VERBOSE
  printf("Reading Input and Output register\n");
  #endif

  address = ARCHI_GPIO_ADDR + GPIO_PADIN_32_63_OFFSET;
  val_rd = pulp_read32(address);
  address = ARCHI_GPIO_ADDR + GPIO_PADOUT_0_31_OFFSET;
  val_rd1 = pulp_read32(address);
  if(val_rd!=(invert(val_rd1))){
    error++ ;
  }
  #ifdef VERBOSE
  printf("in = %x\n", val_rd); // gpio_val);
  printf("out = %x\n", val_rd1);
  printf("exp = %x\n", invert(val_rd1));
  printf("[POST-TEST] errors = %0d\n",error);
  #endif 
  return error;
}
