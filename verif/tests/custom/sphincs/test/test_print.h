#include <stdint.h>

#define UART_REG_TXFIFO ((volatile uint8_t*)(0x10000000))

void print_str(const char *s);

void print_int(int num);

#ifdef PRINT_CYCLES
static inline uint32_t get_cycles(void) {
    uint32_t cycles;
    asm volatile ("csrr %0, mcycle" : "=r" (cycles));
    return cycles;
}
#endif