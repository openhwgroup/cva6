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
  printf("Hello CVA6!\n");
  uart_wait_tx_done();
  return 0;
}
 


