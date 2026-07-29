#include <stdint.h>

// NS16550a Register
#define UART_BASE 0x10000000
#define RBR (*(volatile uint32_t *)(UART_BASE + 0x00))
#define THR (*(volatile uint32_t *)(UART_BASE + 0x00))
#define DLL (*(volatile uint32_t *)(UART_BASE + 0x00))
#define DLM (*(volatile uint32_t *)(UART_BASE + 0x04))
#define LCR (*(volatile uint32_t *)(UART_BASE + 0x0C))
#define LSR (*(volatile uint32_t *)(UART_BASE + 0x14))

void uart_init() {
    LCR = 0x80; // Enable Divisor Latch Access (DLAB=1)
    DLL = 0x1B; // Divisor LSB (27)
    DLM = 0x00; // Divisor MSB (0)
    LCR = 0x03; // Disable DLAB, set 8-bit word length, 1 stop bit, no parity
}

void uart_putchar(char c) {
    while ((LSR & 0x20) == 0);
    THR = c;
}
char uart_getchar() {
    while ((LSR & 0x01) == 0);
    return RBR;
}

void uart_puts(const char* str) {
    while (*str) {
        uart_putchar(*str++);
    }
}

void uart_put_uint32(uint32_t num) {
    if (num == 0) {
        uart_putchar('0');
        return;
    }
    char buf[12];
    int i = 0;
    while (num > 0) {
        buf[i++] = (num % 10) + '0';
        num /= 10;
    }
    while (i > 0) {
        uart_putchar(buf[--i]);
    }
}

uint32_t uart_get_uint32_raw() {
    uint32_t val = 0;
    val |= ((uint32_t)uart_getchar() & 0xFF) << 0;
    val |= ((uint32_t)uart_getchar() & 0xFF) << 8;
    val |= ((uint32_t)uart_getchar() & 0xFF) << 16;
    val |= ((uint32_t)uart_getchar() & 0xFF) << 24;
    return val;
}

int main() {
    uart_init();
    uart_puts("CVA6 UART INITIALIZED. Awaiting data...\r\n");

    while(1) {
        // Wait for 4 bytes for 'a' and 4 bytes for 'b'
        uint32_t a = uart_get_uint32_raw();
        uint32_t b = uart_get_uint32_raw();
        
        uint32_t c = a + b;

        uart_puts("Result: ");
        uart_put_uint32(c);
        uart_puts("\r\n");
    }

    return 0;
}