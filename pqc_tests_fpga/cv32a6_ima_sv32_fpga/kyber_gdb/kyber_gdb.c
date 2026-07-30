#include <stddef.h>
#include <stdint.h>
#include "../../../verif/tests/custom/kyber/kem.h"
#include "../../../verif/tests/custom/kyber/randombytes.h"

#define NTESTS 1


// Bare-Metal UART Driver
#define UART_BASE 0x10000000
#define UART_THR  (*(volatile uint8_t *)(UART_BASE + 0x00)) // Transmitter Holding Register
#define UART_LSR  (*(volatile uint8_t *)(UART_BASE + 0x14)) // Line Status Register

#define UART_IER  (*(volatile uint8_t *)(UART_BASE + 0x04)) // Interrupt Enable Register
#define UART_FCR  (*(volatile uint8_t *)(UART_BASE + 0x08)) // FIFO Control Register
#define UART_LCR  (*(volatile uint8_t *)(UART_BASE + 0x0C)) // Line Control Register
#define UART_DLL  (*(volatile uint8_t *)(UART_BASE + 0x00)) // Divisor Latch LSB
#define UART_DLM  (*(volatile uint8_t *)(UART_BASE + 0x04)) // Divisor Latch MSB

static void uart_sendchar(char c) {
    // Wait until Transmitter Holding Register Empty (THRE) bit is set
    while ((UART_LSR & 0x20) == 0);
    UART_THR = c;
}



static void uart_init(void) {
    // 1. Disable interrupts
    UART_IER = 0x00;
    UART_LCR = 0x80;
    
    // Divisor for 115200 baud 
    UART_DLL = 0x1B;
    UART_DLM = 0x00;
    UART_LCR = 0x03;
    UART_FCR = 0x07;
}

static void print_str(const char *str) {
    while (*str) {
        uart_sendchar(*str++);
    }
}

static void print_int(int val) {
    char buf[16];
    int i = 0;
    
    if (val == 0) {
        uart_sendchar('0');
        return;
    }
    if (val < 0) {
        uart_sendchar('-');
        val = -val;
    }
    while (val > 0) {
        buf[i++] = (val % 10) + '0';
        val /= 10;
    }
    while (i > 0) {
        uart_sendchar(buf[--i]);
    }
}

/* --- Bare-Metal Helpers --- */
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

/* --- Kyber Tests --- */
static int test_keys(void)
{
    uint8_t pk[CRYPTO_PUBLICKEYBYTES];
    uint8_t sk[CRYPTO_SECRETKEYBYTES];
    uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
    uint8_t key_a[CRYPTO_BYTES];
    uint8_t key_b[CRYPTO_BYTES];

    print_str("Generating keypair...\r\n");
    crypto_kem_keypair(pk, sk);

    print_str("Encapsulating secret...\r\n");
    crypto_kem_enc(ct, key_b, pk);

    print_str("Decapsulating secret...\r\n");
    crypto_kem_dec(key_a, ct, sk);

    if(custom_memcmp(key_a, key_b, CRYPTO_BYTES) != 0) {
        print_str("ERROR: Shared secrets do not match!\r\n");
        return 1; 
    }
    
    print_str("Shared secrets match.\r\n");
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
        print_str("ERROR: Decapsulation succeeded with invalid secret key!\r\n");
        return 1;
    }

    print_str("Invalid secret key rejected correctly.\r\n");
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
        print_str("ERROR: Decapsulation succeeded with corrupted ciphertext!\r\n");
        return 1;
    }

    print_str("Invalid ciphertext rejected correctly.\r\n");
    return 0;
}

int main(void)
{
    uart_init();
    unsigned int i;
    int r = 0;

    print_str("\r\n===============================\r\n");
    print_str(" Kyber KEM FPGA Hardware Test\r\n");
    print_str("===============================\r\n");

    for(i = 0; i < NTESTS; i++) {
        print_str("\r\n--- Running Test Iteration ");
        print_int(i + 1);
        print_str(" ---\r\n");

        r |= test_keys();
        r |= test_invalid_sk_a();
        r |= test_invalid_ciphertext();
        
        if(r) {
            print_str("\r\nTEST FAILED\r\n");
            return -1;
        }
    }

    print_str("\r\nALL TESTS PASSED\r\n");

    print_str("CRYPTO_PUBLICKEYBYTES = ");
    print_int(CRYPTO_PUBLICKEYBYTES);
    print_str("\r\nCRYPTO_SECRETKEYBYTES = ");
    print_int(CRYPTO_SECRETKEYBYTES);
    print_str("\r\nCRYPTO_CIPHERTEXTBYTES = ");
    print_int(CRYPTO_CIPHERTEXTBYTES);
    print_str("\r\nCRYPTO_BYTES = ");
    print_int(CRYPTO_BYTES);
    print_str("\r\n");

    return 0;
}