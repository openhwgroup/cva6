/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
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
#include <stdlib.h>
#include <stdint.h>
#include "utils.h"
#include "../../inc/udma/udma.h"
#include "../../inc/udma/spim/udma_spim_v3.h"
#include "flash_page.h"


#define REG_PADFUN0_OFFSET  0x10
#define REG_PADFUN1_OFFSET  0x14
#define REG_PADFUN2_OFFSET  0x18
#define REG_PADFUN3_OFFSET  0x1C
#define REG_PADCFG0_OFFSET  0x24
#define REG_PADCFG1_OFFSET  0x28
#define REG_PADCFG2_OFFSET  0x2C
#define REG_PADCFG3_OFFSET  0x30
#define REG_PADCFG4_OFFSET  0x34
#define REG_PADCFG5_OFFSET  0x38
#define REG_PADCFG6_OFFSET  0x3C
#define REG_PADCFG7_OFFSET  0x40
#define REG_PADCFG8_OFFSET  0x44
#define REG_PADCFG9_OFFSET  0x48
#define REG_PADCFG10_OFFSET 0x4C
#define REG_PADCFG11_OFFSET 0x50
#define REG_PADCFG12_OFFSET 0x54
#define REG_PADCFG13_OFFSET 0x58
#define REG_PADCFG14_OFFSET 0x5C
#define REG_PADCFG15_OFFSET 0x60

#define OUT 1
#define IN  0

#define BUFFER_SIZE 16

#define TEST_PAGE_SIZE 256

int pad_fun_offset[4] = {REG_PADFUN0_OFFSET,REG_PADFUN1_OFFSET,REG_PADFUN2_OFFSET,REG_PADFUN3_OFFSET};
int pad_cfg_offset[16] = {REG_PADCFG0_OFFSET,REG_PADCFG1_OFFSET,REG_PADCFG2_OFFSET,REG_PADCFG3_OFFSET,REG_PADCFG4_OFFSET,REG_PADCFG5_OFFSET,REG_PADCFG6_OFFSET,REG_PADCFG7_OFFSET,REG_PADCFG8_OFFSET,REG_PADCFG9_OFFSET,REG_PADCFG10_OFFSET,REG_PADCFG11_OFFSET,REG_PADCFG12_OFFSET,REG_PADCFG13_OFFSET,REG_PADCFG14_OFFSET,REG_PADCFG15_OFFSET};

static inline void wait_cycles(const unsigned cycles)
{
  /**
   * Each iteration of the loop below will take four cycles on RI5CY (one for
   * `addi` and three for the taken `bnez`; if the instructions hit in the
   * I$).  Thus, we let `i` count the number of remaining loop iterations and
   * initialize it to a fourth of the number of clock cyles.  With this
   * initialization, we must not enter the loop if the number of clock cycles
   * is less than four, because this will cause an underflow on the first
   * subtraction.
   */
  register unsigned threshold;
  asm volatile("li %[threshold], 4" : [threshold] "=r" (threshold));
  asm volatile goto("ble %[cycles], %[threshold], %l2"
          : /* no output */
    : [cycles] "r" (cycles), [threshold] "r" (threshold)
          : /* no clobbers */
    : __wait_cycles_end);
  register unsigned i = cycles >> 2;
  __wait_cycles_start:
  // Decrement `i` and loop if it is not yet zero.
  asm volatile("addi %0, %0, -1" : "+r" (i));
  asm volatile goto("bnez %0, %l1"
          : /* no output */
    : "r" (i)
          : /* no clobbers */
    : __wait_cycles_start);
  __wait_cycles_end:
  return;
}

int main()
{

  int u=0;
  int poll_var=0;

  int *memory_page = (int*) 0x1C003000;
  int *tx_buffer_cmd_program = (int*) 0x1C004000;
  int *addr_buffer = (int*) 0x1C005000;
  int *tx_buffer_cmd_read = (int*) 0x1C006000;
  int *rx_page= (int*) 0x1C007000;
  int *tx_buffer_cmd_erase= (int*) 0x1C008000;
  int *tx_buffer_cmd_read_ID= (int*) 0x1C009000;
  int *tx_buffer_cmd_read_WIP = (int*) 0x1C00A000;
  int *sr1= (int*) 0x1C00B000;
  int *rems_resp= (int*) 0x1C00C000;
//int *error = 0x1C00A000;

  volatile int error=0;
  int temp=0;
  //volatile int rems_resp[6];

//--- refer to this manual for the commands
//--- https://www.cypress.com/file/216421/download

//int addr_buffer[4] = {0x00,0x00,0x00,0x00}; //--- reading address

  for (int i=0; i <260; i++){
    if(i<4)
      memory_page[i] = 0x00;
    else
      memory_page[i] = i-4;
  }


//--- command sequence
/*tx_buffer_cmd_program[BUFFER_SIZE] = {SPI_CMD_CFG(1,0,0),
                                          SPI_CMD_SOT(0),
                                          SPI_CMD_SEND_CMD(0x06,8,0),
                                          SPI_CMD_EOT(0,0),
                                          SPI_CMD_SOT(0),
                                          SPI_CMD_SEND_CMD(0x12,8,0),
                                          SPI_CMD_TX_DATA(4,4,8,0,0), //--- write 4B addr to the addr buffer (first 4 bytes of the "page" array)
                                          SPI_CMD_TX_DATA(TEST_PAGE_SIZE,TEST_PAGE_SIZE,8,0,0), //--- write 256B page data to the page buffer
                                          SPI_CMD_EOT(0,0)}; */

  for (int i=0; i <9; i++){
    switch (i) {
      case 0: 
      tx_buffer_cmd_program[i]= SPI_CMD_CFG(1,0,0);
      break;
      case 1: 
      tx_buffer_cmd_program[i]= SPI_CMD_SOT(0);
      break;
      case 2: 
      tx_buffer_cmd_program[i]= SPI_CMD_SEND_CMD(0x06,8,0); //Write enable
      break;
      case 3: 
      tx_buffer_cmd_program[i]= SPI_CMD_EOT(0,0);
      break;
      case 4: 
      tx_buffer_cmd_program[i]= SPI_CMD_SOT(0);
      break;
      case 5: 
      tx_buffer_cmd_program[i]= SPI_CMD_SEND_CMD(0x12,8,0); //Page program to write 4bytes on he flash
      break;
      case 6: 
      tx_buffer_cmd_program[i]= SPI_CMD_TX_DATA(4,4,8,0,0);
      break;
      case 7: 
      tx_buffer_cmd_program[i]= SPI_CMD_TX_DATA(TEST_PAGE_SIZE,TEST_PAGE_SIZE,8,0,0);
      break;
      case 8: 
      tx_buffer_cmd_program[i]= SPI_CMD_EOT(0,0);
      break;
      default:
      tx_buffer_cmd_program[i]= 0;
      break;
  }
}

//int addr_buffer[4] = {0x00,0x00,0x00,0x00}; //--- reading address

for (int i=0; i <4; i++){
  addr_buffer[i] = 0x00;
}





/*int tx_buffer_cmd_read[BUFFER_SIZE]    = {SPI_CMD_CFG(1,0,0),
                                          SPI_CMD_SOT(0),
                                          SPI_CMD_SEND_CMD(0x13,8,0), //--- read command
                                          SPI_CMD_TX_DATA(4,4,8,0,0), //--- send the read address
                                          SPI_CMD_RX_DATA(TEST_PAGE_SIZE,TEST_PAGE_SIZE,8,0,0),
                                          SPI_CMD_EOT(0,0)};*/

for (int i=0; i <6; i++){
  switch (i) {
    case 0: 
    tx_buffer_cmd_read[i]= SPI_CMD_CFG(1,0,0);
    break;
    case 1: 
    tx_buffer_cmd_read[i]= SPI_CMD_SOT(0);
    break;
    case 2: 
    tx_buffer_cmd_read[i]= SPI_CMD_SEND_CMD(0x13,8,0);
    break;
    case 3: 
    tx_buffer_cmd_read[i]= SPI_CMD_TX_DATA(4,4,8,0,0);
    break;
    case 4: 
    tx_buffer_cmd_read[i]= SPI_CMD_RX_DATA(TEST_PAGE_SIZE,TEST_PAGE_SIZE,8,0,0);
    break;  
    case 5:
    tx_buffer_cmd_read[i]= SPI_CMD_EOT(0,0);
    break;
    default:
    tx_buffer_cmd_read[i]= 0;
    break;
  }
}



/*int tx_buffer_cmd_read_WIP[BUFFER_SIZE] = {SPI_CMD_CFG(1,0,0),
                                           SPI_CMD_SOT(0),
                                           SPI_CMD_SEND_CMD(0x07,8,0),
                                           SPI_CMD_RX_DATA(1,1,8,0,0),
                                           SPI_CMD_EOT(0,0)};*/
for (int i=0; i <5; i++){
  switch (i) {
    case 0: 
    tx_buffer_cmd_read_WIP[i]= SPI_CMD_CFG(1,0,0);
    break;
    case 1: 
    tx_buffer_cmd_read_WIP[i]= SPI_CMD_SOT(0);
    break;
    case 2: 
    tx_buffer_cmd_read_WIP[i]= SPI_CMD_SEND_CMD(0x05,8,0);
    break;
    case 3: 
    tx_buffer_cmd_read_WIP[i]= SPI_CMD_RX_DATA(1,0,8,0,0);
    break;
    case 4: 
    tx_buffer_cmd_read_WIP[i]= SPI_CMD_EOT(0,0);
    break;  
    default:
    tx_buffer_cmd_read_WIP[i]= 0;
    break;
  }
}


/* From corrado test */
/*volatile int sr1;
int tx_buffer_cmd_erase[BUFFER_SIZE] = {SPI_CMD_CFG(1,0,0),
                                           SPI_CMD_SOT(0),
                                           SPI_CMD_SEND_CMD(0x06,8,0),
                                           SPI_CMD_EOT(0,0),
                                           SPI_CMD_SOT(0),
                                           SPI_CMD_SEND_CMD(0x60,8,0),
                                           SPI_CMD_EOT(0,0)};*/

for (int i=0; i <7; i++){
  switch (i) {
    case 0: 
    tx_buffer_cmd_erase[i]= SPI_CMD_CFG(1,0,0);
    break;
    case 1: 
    tx_buffer_cmd_erase[i]= SPI_CMD_SOT(0);
    break;
    case 2: 
    tx_buffer_cmd_erase[i]= SPI_CMD_SEND_CMD(0x06,8,0);
    break;
    case 3: 
    tx_buffer_cmd_erase[i]= SPI_CMD_EOT(0,0);
    break;
    case 4: 
    tx_buffer_cmd_erase[i]= SPI_CMD_SOT(0);
    break;  
    case 5: 
    tx_buffer_cmd_erase[i]= SPI_CMD_SEND_CMD(0x60,8,0);
    break;
    case 6: 
    tx_buffer_cmd_erase[i]= SPI_CMD_EOT(0,0);
    break;  
    default:
    tx_buffer_cmd_erase[i]= 0;
    break;
  }
}



/*int tx_buffer_cmd_read_ID[BUFFER_SIZE]    = {SPI_CMD_CFG(1,0,0),
                                          SPI_CMD_SOT(0),
                                          SPI_CMD_SEND_CMD(0x9F,8,0), //--- read command
                                          SPI_CMD_RX_DATA(6,0,8,0,0),
                                          SPI_CMD_EOT(0,0)};*/

  for (int i=0; i <5; i++){
    switch (i) {
      case 0: 
      tx_buffer_cmd_read_ID[i]= SPI_CMD_CFG(1,0,0);
      break;
      case 1: 
      tx_buffer_cmd_read_ID[i]= SPI_CMD_SOT(0);
      break;
      case 2: 
      tx_buffer_cmd_read_ID[i]= SPI_CMD_SEND_CMD(0x9F,8,0);
      break;
      case 3: 
      tx_buffer_cmd_read_ID[i]= SPI_CMD_RX_DATA(6,0,8,0,0);
      break;
      case 4: 
      tx_buffer_cmd_read_ID[i]= SPI_CMD_EOT(0,0);
      break;  
      default:
      tx_buffer_cmd_read_ID[i]= 0;
      break;
    }
  }

//int rx_page[TEST_PAGE_SIZE];


//FIX PRINTF UART
#ifdef FPGA_EMULATION
    int baud_rate = 9600;
    int test_freq = 10000000;
#else
    int baud_rate = 115200;
    int test_freq = 17500000;
#endif  
    uart_set_cfg(0,(test_freq/baud_rate)>>4);

//for (int u = 0; u<1; u++){

      //printf("[%d, %d] Start test flash page programming over qspi %d\n",  0, 0,u);

      //--- enable all the udma channels
    plp_udma_cg_set(plp_udma_cg_get() | (0xffffffff));
    barrier();

      //--- get the base address of the SPIMx udma channels
    unsigned int udma_spim_channel_base = hal_udma_channel_base(UDMA_CHANNEL_ID(ARCHI_UDMA_SPIM_ID(u)));
      //printf("uDMA spim%d base channel address %8x\n", u,udma_spim_channel_base);
    barrier();

      //--- write the flash page

      /*printf("uDMA spim%d TX Saddr: %8x\n", u,UDMA_SPIM_TX_ADDR(u));
      printf("uDMA spim%d (int)page): %8x\n", u,(int)page);

      printf("uDMA spim%d CMD Saddr: %8x\n", u, UDMA_SPIM_CMD_ADDR(u));
      printf("uDMA spim%d (uint32_t)tx_buffer_cmd_program : %8x\n", u,(int)tx_buffer_cmd_program );*/


      //--- check flash ID for debugging (refer to the manual)
    for(int i = 0; i < 6; i++) {
      rems_resp[i] = 0;
    }

    plp_udma_enqueue(UDMA_SPIM_RX_ADDR(u) ,  (unsigned int)rems_resp, 6*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
    barrier();
    plp_udma_enqueue(UDMA_SPIM_CMD_ADDR(u),  (int)tx_buffer_cmd_read_ID, 5*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
    //--- polling to check if the transfer is completed (when the "SADDR" register of the SPI channel is equal to 0)
    do {
      poll_var = pulp_read32(UDMA_CHANNEL_SIZE_OFFSET + UDMA_SPIM_RX_ADDR(u));
      barrier();
      poll_var = pulp_read32(UDMA_CHANNEL_SADDR_OFFSET + UDMA_SPIM_RX_ADDR(u));
      barrier();
    } while(poll_var != 0);

    //Write the Flash page
    plp_udma_enqueue(UDMA_SPIM_TX_ADDR(u) ,  (int)memory_page          ,TEST_PAGE_SIZE*4 + 4*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
    barrier();
    plp_udma_enqueue(UDMA_SPIM_CMD_ADDR(u),  (int)tx_buffer_cmd_program , 9*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
    barrier();
    printf("write flash, done\n");
      //--- wait until the page is written (we could use the WIP bit instead of waiting)
    //wait_cycles(500000);
      //--- check WIP ("Work-In-Progress" flag of the "Status Register 1" of the flash memory)
    temp=0;
    pulp_write32(sr1,0);
    do {
      
      plp_udma_enqueue(UDMA_SPIM_RX_ADDR(u) ,  (unsigned int)sr1, 1*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
      barrier();
      plp_udma_enqueue(UDMA_SPIM_CMD_ADDR(u),  (int)tx_buffer_cmd_read_WIP, 5*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
      barrier();
      //--- polling to check if the transfer is completed (when the "SADDR" register of the SPI channel is equal to 0)
      do {
        poll_var = pulp_read32(UDMA_CHANNEL_SIZE_OFFSET + UDMA_SPIM_RX_ADDR(u));
        barrier();
        poll_var = pulp_read32(UDMA_CHANNEL_SADDR_OFFSET + UDMA_SPIM_RX_ADDR(u));
        barrier();
      } while(poll_var != 0);
      temp=pulp_read32(sr1);
      barrier();
      temp &=1;
      barrier();
    } while( temp != 0);




    barrier();
    printf ("Ready to read back\n");


      /*printf("uDMA spim%d RX Saddr: %8x\n", u,UDMA_SPIM_RX_ADDR(u));
      printf("uDMA spim%d (uint32_t)rx_page: %8x\n", u,(int)rx_page);

      printf("uDMA spim%d TX Saddr: %8x\n", u,UDMA_SPIM_TX_ADDR(u));
      printf("uDMA spim%d (uint32_t)addr_buffer : %8x\n", u,(int)addr_buffer );

      printf("uDMA spim%d CMD Saddr: %8x\n", u,UDMA_SPIM_CMD_ADDR(u));
      printf("uDMA spim%d (uint32_t)tx_buffer_cmd_read : %8x\n", u,(int)tx_buffer_cmd_read);*/

      //--- try to read back data
    plp_udma_enqueue(UDMA_SPIM_RX_ADDR(u) ,  (int)rx_page     , TEST_PAGE_SIZE*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
    barrier();

    plp_udma_enqueue(UDMA_SPIM_TX_ADDR(u) ,  (int)addr_buffer    , 4*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
    barrier();

    plp_udma_enqueue(UDMA_SPIM_CMD_ADDR(u),  (int)tx_buffer_cmd_read , 6*4, UDMA_CHANNEL_CFG_EN | UDMA_CHANNEL_CFG_SIZE_32);
    barrier();
    printf("ok\n");

      //wait_cycles(25000);

      //--- polling to check if the transfer is completed (when the "SADDR" register of the SPI channel is equal to 0)
    do {
      poll_var = pulp_read32(UDMA_CHANNEL_SIZE_OFFSET + UDMA_SPIM_RX_ADDR(u));
      barrier();
      poll_var = pulp_read32(UDMA_CHANNEL_SADDR_OFFSET + UDMA_SPIM_RX_ADDR(u));
      barrier();
    } while(poll_var != 0);


    barrier();


    for (int i = 0; i < TEST_PAGE_SIZE; ++i)
    {
      //printf("Index %d: read %8x, expected %8x \n",i,rx_page[i],memory_page[i+4]);
      if (rx_page[i] != memory_page[i+4])
      {
        error++;
      }
    }

//}
    if (error == 0)
    {
      printf("test passed\n");
    }else{
      printf("test failed with %d errors\n", error);
    }
    uart_wait_tx_done();

    return error;
}
