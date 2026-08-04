#include "test_print.h"
#include <stdint.h>

void print_str(const char *s) {
    while (*s) {
        *UART_REG_TXFIFO = *s++;
    }
}

void print_int(int num) {
    char buf[12];
    int i = 0;

    if (num == 0) {
        *UART_REG_TXFIFO = '0';
        return;
    }

    if (num < 0) {
        *UART_REG_TXFIFO = '-';
        num = -num;
    }

    while (num > 0) {
        buf[i++] = (num % 10) + '0';
        num /= 10;
    }

    while (i > 0) {
        *UART_REG_TXFIFO = buf[--i];
    }
}