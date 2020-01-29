#include <string.h>
#include "uart.h"
#include "diskio.h"

int main()
{
    int ch;
    uint8_t *buff = (uint8_t *)0x80000000UL;
    init_uart(50000000, 115200);
    hello();
    disk_initialize (0);
    disk_read(0, buff, 0, 1);
    do {
      ch = get_uart_byte();
      if (ch != -1) write_serial(ch);
    } while (ch != '\r');
    finish();

    while (1)
    {
        // do nothing
    }
}

void handle_trap(void)
{
    // print_uart("trap\r\n");
}
