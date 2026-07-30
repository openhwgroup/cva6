#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include "../falcon.h"

// Hornet Debug Interface
#define DEBUG_IF_ADDR 0x10008010
#define DEBUG_REG     ((volatile char *)DEBUG_IF_ADDR)

// Falcon configuration for testing
#define LOGN 9 // FN-512

int main(void) {
    // Deterministic PRNG
    shake256_context rng;
    // We do not have RNG hardware, so we initialize the PRNG from a determined seed 
    // Check get_seed() in rng.c, we set 0xFF 
    shake256_init_prng_from_system(&rng); 

    // Allocate memory in bare-metal
    size_t tmp_size = FALCON_TMPSIZE_KEYGEN(LOGN);
    if (FALCON_TMPSIZE_SIGNDYN(LOGN) > tmp_size) {
        tmp_size = FALCON_TMPSIZE_SIGNDYN(LOGN);
    }
    
    // Force 8-byte alignment for RISC-V floating-point emulation buffers
    __attribute__((aligned(8))) uint8_t tmp[tmp_size];
    uint8_t privkey[FALCON_PRIVKEY_SIZE(LOGN)];
    uint8_t pubkey[FALCON_PUBKEY_SIZE(LOGN)];
    
    // Print in TCL console
    *DEBUG_REG = 'S'; // 'S' for Start, 32'd83
    
    int result = falcon_keygen_make(&rng, LOGN, privkey, sizeof(privkey), 
                                    pubkey, sizeof(pubkey), tmp, tmp_size);

    if (result == 0) {
        *DEBUG_REG = 'P'; // 'P' for Pass, 32'd80 
    } else {
        *DEBUG_REG = 'F'; // 'F' for Fail, 32'd70
    }

    while(1) { 
        __asm__ volatile ("nop"); 
    }

    return 0; 
}