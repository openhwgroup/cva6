#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

#include "../../../verif/tests/custom/sphincs/api.h"
#include "../../../verif/tests/custom/sphincs/params.h"
#include "../../../verif/tests/custom/sphincs/randombytes.h"
#include "../../../verif/tests/custom/sphincs/test/test_syscalls.h"

#define SPX_MLEN 32
#define SPX_SIGNATURES 1


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

int main()
{
    uart_init();
    uart_puts("CVA6 UART INITIALIZED. Waiting for trigger...\r\n");

    // Block until the Python script sends a trigger byte
    while (uart_getchar() != 'c');

    int ret = 0;
    int i;

    uart_puts("\r\n==================================\r\n");
    uart_puts(" SPHINCS+ FPGA Hardware Test\r\n");
    uart_puts("==================================\r\n");


    unsigned char pk[SPX_PK_BYTES];
    unsigned char sk[SPX_SK_BYTES];
    unsigned char m[SPX_MLEN];
    unsigned char sm[SPX_BYTES + SPX_MLEN];
    unsigned char mout[SPX_BYTES + SPX_MLEN];
    unsigned long long smlen;
    unsigned long long mlen;
    uint32_t start_cycles;
    uint32_t end_cycles;

    randombytes(m, SPX_MLEN);

    uart_puts("Generating keypair...\r\n");
    start_cycles = get_cycles();
    int r_keypair = crypto_sign_keypair(pk, sk);
    end_cycles = get_cycles();
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");

    if (r_keypair) {
        uart_puts("Keypair generation failed!\r\n");
        return -1;
    }
    uart_puts("Keypair generation successful.\r\n");

    uart_puts("Testing ");
    uart_put_uint32(SPX_SIGNATURES);
    uart_puts(" signatures.. \r\n");

    for (i = 0; i < SPX_SIGNATURES; i++) {
        printf("  - iteration #%d:\r\n", i);
        uart_puts("  - iteration #");
        uart_put_uint32(i);
        uart_puts(":\r\n");

        uart_puts("Signing message...");
        start_cycles = get_cycles();
        crypto_sign(sm, &smlen, m, SPX_MLEN, sk);
        end_cycles = get_cycles();
        uart_puts(" -> Cycles: ");
        uart_put_uint32(end_cycles - start_cycles);
        uart_puts("\r\n");

        if (smlen != SPX_BYTES + SPX_MLEN) {
            uart_puts("smlen incorrect\r\n");
            ret = -1;
        }
        else {
            uart_puts("smlen as expected.\r\n");
        }

        /* Test if signature is valid. */
        uart_puts("Verifying message...\r\n");
        start_cycles = get_cycles();
        int r_sign_open = crypto_sign_open(mout, &mlen, sm, smlen, pk);
        end_cycles = get_cycles();
        uart_puts(" -> Cycles: ");
        uart_put_uint32(end_cycles - start_cycles);
        uart_puts("\r\n");
        
        if (r_sign_open) {
            uart_puts("Verification failed!\r\n");
            ret = -1;
        }
        else {
            uart_puts("Verification succeeded.\r\n");
        }

        /* Test if the correct message was recovered. */
        if (mlen != SPX_MLEN) {
            uart_puts("mlen incorrect!\r\n");
            ret = -1;
        }
        else {
            uart_puts("mlen as expected.\r\n");
        }
        if (memcmp(m, mout, SPX_MLEN)) {
            uart_puts("Output message incorrect!\r\n");
            ret = -1;
        }
        else {
            uart_puts("Output message as expected.\r\n");
        }

        /* Test if signature is valid when validating in-place. */
        if (crypto_sign_open(sm, &mlen, sm, smlen, pk)) {
            uart_puts("In-place verification failed!\r\n");
            ret = -1;
        }
        else {
            uart_puts("In-place verification succeeded.\r\n");
        }

        /* Test if flipping bits invalidates the signature (it should). */

        /* Flip the first bit of the message. Should invalidate. */
        sm[smlen - 1] ^= 1;
        if (!crypto_sign_open(mout, &mlen, sm, smlen, pk)) {
            uart_puts("Flipping a bit of m DID NOT invalidate signature!\r\n");
            ret = -1;
        }
        else {
            uart_puts("Flipping a bit of m invalidates signature.\r\n");
        }
        sm[smlen - 1] ^= 1;

#ifdef SPX_TEST_INVALIDSIG
        int j;
        /* Flip one bit per hash; the signature is entirely hashes. */
        for (j = 0; j < (int)(smlen - SPX_MLEN); j += SPX_N) {
            sm[j] ^= 1;
            if (!crypto_sign_open(mout, &mlen, sm, smlen, pk)) {
                uart_puts("Flipping bit ");
                uart_put_uint32(j);
                uart_puts(" DID NOT invalidate sig + m!\r\n");
                sm[j] ^= 1;
                ret = -1;
                break;
            }
            sm[j] ^= 1;
        }
        if (j >= (int)(smlen - SPX_MLEN)) {
            uart_puts("Changing any signature hash invalidates signature.\r\n");
        }
#endif
    }

    uart_puts("\r\nALL TESTS PASSED\r\n");

    return ret;
}
