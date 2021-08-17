//#include "util.h"
#include <stdio.h>
#include <stdlib.h>
#include "utils.h"
//#define FPGA_EMULATION

int main(int argc, char const *argv[]) {

  #ifdef FPGA_EMULATION
  int baud_rate = 9600;
  int test_freq = 10000000;
  #else
  int baud_rate = 115200;
  int test_freq = 17500000;
  #endif  
  uart_set_cfg(0,(test_freq/baud_rate)>>4);
  uint32_t * hyaxicfg_reg_mask = 0xC1004018;
  pulp_write32(hyaxicfg_reg_mask,26); //128MB addressable
  uint32_t * hyaxicfg_reg_memspace = 0xC1004024;
  pulp_write32(hyaxicfg_reg_memspace,0x84000000); // Changing RAM end address, 64 MB
  printf("Hello CVA6!\n");
  uart_wait_tx_done();
  return 0;
}
 


