#include <stddef.h>
#include <stdint.h>
#include "../../../verif/tests/custom/dilithium/sign.h"
#include "../../../verif/tests/custom/dilithium/randombytes.h"

#define MLEN 59
#define CTXLEN 14
#define NTESTS 1

// NS16550a and UART Register
#define UART_BASE 0x10000000
#define RBR (*(volatile uint32_t *)(UART_BASE + 0x00))
#define THR (*(volatile uint32_t *)(UART_BASE + 0x00))
#define DLL (*(volatile uint32_t *)(UART_BASE + 0x00))
#define DLM (*(volatile uint32_t *)(UART_BASE + 0x04))
#define LCR (*(volatile uint32_t *)(UART_BASE + 0x0C))
#define LSR (*(volatile uint32_t *)(UART_BASE + 0x14))

// UART Functions
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

// Cycle Counting Function
static inline uint32_t get_cycles(void) {
    uint32_t cycles;
    asm volatile ("csrr %0, mcycle" : "=r" (cycles));
    return cycles;
}

// Dilithium Core Test
static int test_dilithium(void)
{
    size_t mlen, smlen;
    uint8_t b;
    uint8_t ctx[CTXLEN] = {0};
    uint8_t m[MLEN + CRYPTO_BYTES];
    uint8_t m2[MLEN + CRYPTO_BYTES];
    uint8_t sm[MLEN + CRYPTO_BYTES];
    uint8_t pk[CRYPTO_PUBLICKEYBYTES];
    uint8_t sk[CRYPTO_SECRETKEYBYTES];
    
    size_t j;
    int ret;
    uint32_t start_cycles, end_cycles;

    uart_puts("Generating random message...\r\n");
    randombytes(m, MLEN);

    uart_puts("Generating keypair...\r\n");
    start_cycles = get_cycles();
    crypto_sign_keypair(pk, sk);
    end_cycles = get_cycles();
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");

    uart_puts("Signing message...\r\n");
    start_cycles = get_cycles();
    crypto_sign(sm, &smlen, m, MLEN, ctx, CTXLEN, sk);
    end_cycles = get_cycles();
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");
    
    uart_puts("Verifying message...\r\n");
    start_cycles = get_cycles();
    ret = crypto_sign_open(m2, &mlen, sm, smlen, ctx, CTXLEN, pk);
    end_cycles = get_cycles();
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");

    if(ret) {
        uart_puts("ERROR: Verification failed\r\n");
        return -1;
    }
    
    if(smlen != MLEN + CRYPTO_BYTES) {
        uart_puts("ERROR: Signed message lengths wrong\r\n");
        return -1;
    }

    if(mlen != MLEN) {
        uart_puts("ERROR: Message lengths wrong\r\n");
        return -1;
    }
    
    for(j = 0; j < MLEN; ++j) {
        if(m2[j] != m[j]) {
            uart_puts("ERROR: Messages don't match\r\n");
            return -1;
        }
    }
    uart_puts("Signature valid and messages match.\r\n");

    // Forgery test
    uart_puts("Testing trivial forgeries...\r\n");
    randombytes((uint8_t *)&j, sizeof(j));
    do {
        randombytes(&b, 1);
    } while(!b);
    sm[j % (MLEN + CRYPTO_BYTES)] += b;
    
    ret = crypto_sign_open(m2, &mlen, sm, smlen, ctx, CTXLEN, pk);
    if(!ret) {
        uart_puts("ERROR: Trivial forgeries possible\r\n");
        return -1;
    }
    uart_puts("Forged signatures rejected correctly.\r\n");

    return 0;
}

// Main Entry Point
int main() {
    uart_init();
    uart_puts("CVA6 UART INITIALIZED. Waiting for trigger...\r\n");

    // Block until the Python script sends a trigger byte
    while (uart_getchar() != 'c');

    unsigned int i;
    int r = 0;

    uart_puts("\r\n==================================\r\n");
    uart_puts(" Dilithium FPGA Hardware Test\r\n");
    uart_puts("==================================\r\n");

    for(i = 0; i < NTESTS; i++) {
        uart_puts("\r\n--- Running Test Iteration ");
        uart_put_uint32(i + 1);
        uart_puts(" ---\r\n");

        r |= test_dilithium();
        
        if(r) {
            uart_puts("\r\nTEST FAILED\r\n");
            return -1;
        }
    }

    uart_puts("\r\nALL TESTS PASSED\r\n");

    uart_puts("CRYPTO_PUBLICKEYBYTES = ");
    uart_put_uint32(CRYPTO_PUBLICKEYBYTES);
    uart_puts("\r\nCRYPTO_SECRETKEYBYTES = ");
    uart_put_uint32(CRYPTO_SECRETKEYBYTES);
    uart_puts("\r\nCRYPTO_BYTES = ");
    uart_put_uint32(CRYPTO_BYTES);
    uart_puts("\r\n");

    return 0;
}