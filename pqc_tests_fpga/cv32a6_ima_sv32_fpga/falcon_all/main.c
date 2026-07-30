#include <stddef.h>
#include <stdint.h>
#include "../../../verif/tests/custom/falcon/falcon.h"

// Falcon configuration
#define LOGN 9 // Falcon-512
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

// Falcon Core Test
static int test_falcon(void)
{
    int ret;
    uint32_t start_cycles, end_cycles;

    // Initialize Deterministic PRNG
    shake256_context rng;
    shake256_init_prng_from_system(&rng); 

    // Calculate maximum temporary buffer size required across all operations
    size_t tmp_size = FALCON_TMPSIZE_KEYGEN(LOGN);
    if (FALCON_TMPSIZE_SIGNDYN(LOGN) > tmp_size) {
        tmp_size = FALCON_TMPSIZE_SIGNDYN(LOGN);
    }
    if (FALCON_TMPSIZE_VERIFY(LOGN) > tmp_size) {
        tmp_size = FALCON_TMPSIZE_VERIFY(LOGN);
    }

    // Force 8-byte alignment for RISC-V floating-point emulation buffers
    __attribute__((aligned(8))) uint8_t tmp[tmp_size];
    
    // Key buffers
    uint8_t privkey[FALCON_PRIVKEY_SIZE(LOGN)];
    uint8_t pubkey[FALCON_PUBKEY_SIZE(LOGN)];
    
    // Message and Signature buffers
    uint8_t msg[] = "Falcon Hardware-in-the-Loop Test on CVA6";
    size_t msg_len = sizeof(msg);
    uint8_t sig[FALCON_SIG_COMPRESSED_MAXSIZE(LOGN)];
    size_t sig_len = sizeof(sig);

    uart_puts("Generating keypair...\r\n");
    start_cycles = get_cycles();
    ret = falcon_keygen_make(&rng, LOGN, 
                             privkey, sizeof(privkey), 
                             pubkey, sizeof(pubkey), 
                             tmp, tmp_size);
    end_cycles = get_cycles();
    
    if (ret != 0) {
        uart_puts("ERROR: Keypair generation failed\r\n");
        return -1;
    }
    
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");

    uart_puts("Signing message...\r\n");
    start_cycles = get_cycles();
    ret = falcon_sign_dyn(&rng, sig, &sig_len, FALCON_SIG_COMPRESSED, 
                          privkey, sizeof(privkey), 
                          msg, msg_len, 
                          tmp, tmp_size);
    end_cycles = get_cycles();
    
    if (ret != 0) {
        uart_puts("ERROR: Signature generation failed\r\n");
        return -1;
    }

    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");
    
    uart_puts("Verifying message...\r\n");
    start_cycles = get_cycles();
    ret = falcon_verify(sig, sig_len, FALCON_SIG_COMPRESSED, 
                        pubkey, sizeof(pubkey), 
                        msg, msg_len, 
                        tmp, tmp_size);
    end_cycles = get_cycles();

    if(ret != 0) {
        uart_puts("ERROR: Verification failed\r\n");
        return -1;
    }
    
    uart_puts(" -> Cycles: ");
    uart_put_uint32(end_cycles - start_cycles);
    uart_puts("\r\n");
    uart_puts("Signature valid and messages match.\r\n");

    // Forgery test
    uart_puts("Testing trivial forgeries...\r\n");
    sig[0] ^= 1; // Flip a bit in the signature
    ret = falcon_verify(sig, sig_len, FALCON_SIG_COMPRESSED, 
                        pubkey, sizeof(pubkey), 
                        msg, msg_len, 
                        tmp, tmp_size);
    
    if(ret == 0) {
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
    uart_puts(" Falcon FPGA Hardware Test\r\n");
    uart_puts("==================================\r\n");

    for(i = 0; i < NTESTS; i++) {
        uart_puts("\r\n--- Running Test Iteration ");
        uart_put_uint32(i + 1);
        uart_puts(" ---\r\n");

        r |= test_falcon();
        
        if(r) {
            uart_puts("\r\nTEST FAILED\r\n");
            return -1;
        }
    }

    uart_puts("\r\nALL TESTS PASSED\r\n");

    uart_puts("FALCON_PUBLICKEYBYTES = ");
    uart_put_uint32(FALCON_PUBKEY_SIZE(LOGN));
    uart_puts("\r\nFALCON_SECRETKEYBYTES = ");
    uart_put_uint32(FALCON_PRIVKEY_SIZE(LOGN));
    uart_puts("\r\n");

    return 0;
}