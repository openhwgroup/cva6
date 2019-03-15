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
    uint64_t raw_addr = PITON_SD_BASE_ADDR;
    raw_addr += ((uint64_t)src_lba) << 9;

    uint64_t * addr = (uint64_t *)raw_addr;
    volatile uint64_t * p = (uint64_t *)dst;
    for (uint32_t blk = 0; blk < size; blk++) {
        if(blk % 100 == 0) {
          print_uart("copying block ");
          print_uart_dec(blk, 1);
          print_uart(" of ");
          print_uart_dec(size, 1);
          print_uart(" blocks (");
          print_uart_dec((blk*100)/size, 1);
          print_uart(" %)\r\n");
        }
        for (uint32_t offset = 0; offset < 64; offset++) {
            *(p++) = *(addr++);
        }
    }

    return 0;
}
