#include "uart.h"
#include "spi.h"
#include "sd.h"
#include "gpt.h"

int main()
{
    init_uart();
    print_uart("Hello World!\r\n");

    int res = gpt_find_boot_partition((uint8_t *)0x80000000UL, 2 * 16384);

    if (res == 0)
    {
        // jump to the address
        __asm__ volatile(
            "li s0, 0x80000000;"
            "la a1, _dtb;"
            "jr s0");
    }

    while (1)
    {
        // do nothing
    }
}

void handle_trap(void)
{
    // print_uart("trap\r\n");
}