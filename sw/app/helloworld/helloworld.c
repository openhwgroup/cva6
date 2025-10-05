#include <stdint.h>
#include "uart.h"
  
int main(void)
  {
     uint8_t message[12] = "Hello World\n\r";
     UART_init(&g_uart_0,
             UART_57600_BAUD,
             UART_DATA_8_BITS | UART_NO_PARITY | UART_ONE_STOP_BIT);
    //  while(1){                   
         UART_polled_tx_string(&g_uart_0, message);

         while(UART_tx_complete(&g_uart_0)==0);
    //  }
     return(0);
  }
