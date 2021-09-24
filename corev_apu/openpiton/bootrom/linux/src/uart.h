#pragma once

#include <stdint.h>

#define UART_BASE 0xFFF0C2C000

#define UART_RBR UART_BASE + 0
#define UART_THR UART_BASE + 0
#define UART_INTERRUPT_ENABLE UART_BASE + 1
#define UART_INTERRUPT_IDENT UART_BASE + 2
#define UART_FIFO_CONTROL UART_BASE + 2
#define UART_LINE_CONTROL UART_BASE + 3
#define UART_MODEM_CONTROL UART_BASE + 4
#define UART_LINE_STATUS UART_BASE + 5
#define UART_MODEM_STATUS UART_BASE + 6
#define UART_DLAB_LSB UART_BASE + 0
#define UART_DLAB_MSB UART_BASE + 1

void init_uart();

int print_uart(const char* str);

int print_uart_dec(uint32_t val, uint32_t digits);

int print_uart_int(uint32_t addr);

int print_uart_addr(uint64_t addr);

int print_uart_byte(uint8_t byte);
