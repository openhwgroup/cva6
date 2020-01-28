#include <string.h>
#include "uart.h"
#include "spi.h"
#include "sd.h"
#include "gpt.h"

int main()
{
    int i, ch;
    const char *cur = "Hello World!\r\n\n\n\n";
    init_uart(50000000, 115200);
    for (i = 0; i < strlen(cur); i += 4)
      {
      write_reg_u8(UART_THR, cur[i]);
      write_reg_u8(UART_THR, cur[i+1]);
      write_reg_u8(UART_THR, cur[i+2]);
      write_reg_u8(UART_THR, cur[i+3]);
      }
    ch = read_reg_u8(UART_RBR);
    
    do {
      ch = get_uart_byte();
      if (ch != -1) write_serial(ch);
    } while (ch != '\r');
    write_reg_u8(UART_SIM_FINISH, 0);

#if 0    
        
    int res = gpt_find_boot_partition((uint8_t *)0x80000000UL, 2 * 16384);

    if (res == 0)
    {
        // jump to the address
        __asm__ volatile(
            "li s0, 0x80000000;"
            "la a1, _dtb;"
            "jr s0");
    }
#endif
    while (1)
    {
        // do nothing
    }
}

void handle_trap(void)
{
    // print_uart("trap\r\n");
}
