#include <stddef.h>
#include <stdint.h>
#include "../../../verif/tests/custom/kyber/kem.h"
#include "../../../verif/tests/custom/kyber/randombytes.h"

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

uint32_t uart_get_uint32_raw() {
    uint32_t val = 0;
    val |= ((uint32_t)uart_getchar() & 0xFF) << 0;
    val |= ((uint32_t)uart_getchar() & 0xFF) << 8;
    val |= ((uint32_t)uart_getchar() & 0xFF) << 16;
    val |= ((uint32_t)uart_getchar() & 0xFF) << 24;
    return val;
}

// Bare-Metal Helpers
static int custom_memcmp(const void *s1, const void *s2, size_t n) {
    const unsigned char *p1 = s1;
    const unsigned char *p2 = s2;
    for (size_t i = 0; i < n; i++) {
        if (p1[i] != p2[i]) {
            return p1[i] - p2[i];
        }
    }
    return 0;
}

// Cycle Counting Function
static inline uint32_t get_cycles(void) {
    uint32_t cycles;
    asm volatile ("csrr %0, mcycle" : "=r" (cycles));
    return cycles;
}

// Kyber Functions
static int test_keys(void)
{
    uint8_t pk[CRYPTO_PUBLICKEYBYTES];
    uint8_t sk[CRYPTO_SECRETKEYBYTES];
    uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
    uint8_t key_a[CRYPTO_BYTES];
    uint8_t key_b[CRYPTO_BYTES];
    
    uint32_t start_cycles, end_cycles;

    uart_puts("Generating keypair...\r\n");
    start_cycles = get_cycles();
    crypto_kem_keypair(pk, sk);
    end_cycles = get_cycles();
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");

    uart_puts("Encapsulating secret...\r\n");
    start_cycles = get_cycles();
    crypto_kem_enc(ct, key_b, pk);
    end_cycles = get_cycles();
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");

    uart_puts("Decapsulating secret...\r\n");
    start_cycles = get_cycles();
    crypto_kem_dec(key_a, ct, sk);
    end_cycles = get_cycles();
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");

    if(custom_memcmp(key_a, key_b, CRYPTO_BYTES) != 0) {
        uart_puts("ERROR: Shared secrets do not match!\r\n");
        return 1; 
    }
    
    uart_puts("Shared secrets match.\r\n");
    return 0; 
}

static int test_invalid_sk_a(void)
{
    uint8_t pk[CRYPTO_PUBLICKEYBYTES];
    uint8_t sk[CRYPTO_SECRETKEYBYTES];
    uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
    uint8_t key_a[CRYPTO_BYTES];
    uint8_t key_b[CRYPTO_BYTES];

    crypto_kem_keypair(pk, sk);
    crypto_kem_enc(ct, key_b, pk);

    randombytes(sk, CRYPTO_SECRETKEYBYTES);
    crypto_kem_dec(key_a, ct, sk);

    if(custom_memcmp(key_a, key_b, CRYPTO_BYTES) == 0) {
        uart_puts("ERROR: Decapsulation succeeded with invalid secret key!\r\n");
        return 1;
    }

    uart_puts("Invalid secret key rejected correctly.\r\n");
    return 0;
}

static int test_invalid_ciphertext(void)
{
    uint8_t pk[CRYPTO_PUBLICKEYBYTES];
    uint8_t sk[CRYPTO_SECRETKEYBYTES];
    uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
    uint8_t key_a[CRYPTO_BYTES];
    uint8_t key_b[CRYPTO_BYTES];
    uint8_t b;
    size_t pos;

    do {
        randombytes(&b, sizeof(uint8_t));
    } while(!b);
    randombytes((uint8_t *)&pos, sizeof(size_t));

    crypto_kem_keypair(pk, sk);
    crypto_kem_enc(ct, key_b, pk);

    ct[pos % CRYPTO_CIPHERTEXTBYTES] ^= b;
    crypto_kem_dec(key_a, ct, sk);

    if(custom_memcmp(key_a, key_b, CRYPTO_BYTES) == 0) {
        uart_puts("ERROR: Decapsulation succeeded with corrupted ciphertext!\r\n");
        return 1;
    }

    uart_puts("Invalid ciphertext rejected correctly.\r\n");
    return 0;
}

// Main
int main() {
    uart_init();
    uart_puts("CVA6 UART INITIALIZED. Waiting for trigger...\r\n");

    // Block until the Python script sends a trigger byte
    while (uart_getchar() != 'c');

    unsigned int i;
    int r = 0;

    uart_puts("\r\n===============================\r\n");
    uart_puts(" Kyber KEM FPGA Hardware Test\r\n");
    uart_puts("===============================\r\n");

    for(i = 0; i < NTESTS; i++) {
        uart_puts("\r\n--- Running Test Iteration ");
        uart_put_uint32(i + 1);
        uart_puts(" ---\r\n");

        r |= test_keys();
        r |= test_invalid_sk_a();
        r |= test_invalid_ciphertext();
        
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
    uart_puts("\r\nCRYPTO_CIPHERTEXTBYTES = ");
    uart_put_uint32(CRYPTO_CIPHERTEXTBYTES);
    uart_puts("\r\nCRYPTO_BYTES = ");
    uart_put_uint32(CRYPTO_BYTES);
    uart_puts("\r\n");

    return 0;
}