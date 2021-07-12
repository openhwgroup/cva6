//#include "util.h"
#include <stdio.h>
#include <stdlib.h>
#include "utils.h"

int main(int argc, char const *argv[]) {

  int baud_rate = 115200;
  int test_freq = 50000000; 
  uart_set_cfg(0,(test_freq/baud_rate)/16);
  printf("Hello CVA6!\n");
  uart_wait_tx_done();
  return 0;
}
 
