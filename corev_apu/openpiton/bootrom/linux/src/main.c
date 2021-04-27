#include "uart.h"
#include "spi.h"
#include "sd.h"
#include "gpt.h"
#include "info.h"

int main()
{
    init_uart(UART_FREQ, 115200);
    print_uart(info);

    print_uart("sd initialized!\r\n");

    int res = gpt_find_boot_partition((uint8_t *)0x80000000UL, 2 * 16384);

    return 0;
}

void handle_trap(void)
{
    // print_uart("trap\r\n");
}