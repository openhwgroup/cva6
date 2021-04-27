#include "sd.h"
#include "uart.h"

#ifndef PITON_SD_BASE_ADDR
#define PITON_SD_BASE_ADDR  0xf000000000L
#endif

#ifndef PITON_SD_LENGTH
#define PITON_SD_LENGTH     0xff0300000L
#endif

int init_sd()
{
    print_uart("initializing SD... \r\n");
    return 0;
}

int sd_copy(void *dst, uint32_t src_lba, uint32_t size)
{
    char buf[100];
    uint64_t raw_addr = PITON_SD_BASE_ADDR;
    raw_addr += ((uint64_t)src_lba) << 9;
    uint32_t num_chars = 0;
    uint64_t * addr = (uint64_t *)raw_addr;
    volatile uint64_t * p = (uint64_t *)dst;
    for (uint32_t blk = 0; blk < size; blk++) {
        if(blk % 100 == 0) {
          for(uint32_t k=0; k<num_chars; k++) {
            print_uart("\b");
          }
          num_chars =print_uart("copying block ");
          num_chars+=print_uart_dec(blk, 1);
          num_chars+=print_uart(" of ");
          num_chars+=print_uart_dec(size, 1);
          num_chars+=print_uart(" blocks (");
          num_chars+=print_uart_dec((blk*100)/size, 1);
          num_chars+=print_uart(" %)");
        }
        for (uint32_t offset = 0; offset < 64; offset++) {
            *(p++) = *(addr++);
        }
    }

    print_uart("\r\n");

    return 0;
}
