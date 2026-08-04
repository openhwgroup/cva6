#include <stddef.h>
#include <stdint.h>
#include "randombytes.h"
#include "fips202.h" // Leverage Kyber's native SHAKE256 implementation

// A static seed for deterministic testing on FPGA.
// In a production environment, this would be seeded by a hardware TRNG.
static uint8_t prng_state[32] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F
};

void randombytes(uint8_t *out, size_t outlen) {
    // We need 'outlen' bytes for the caller, plus 32 bytes to update our state.
    // Variable length arrays (VLAs) are supported in C99, which riscv-gcc handles well.
    uint8_t buffer[outlen + 32];
    
    // Hash the current state to generate pseudo-random output
    shake256(buffer, outlen + 32, prng_state, 32);
    
    // Copy the requested random bytes to the output pointer
    for(size_t i = 0; i < outlen; i++) {
        out[i] = buffer[i];
    }
    
    // Use the remaining 32 bytes to update the PRNG state for the next call
    for(size_t i = 0; i < 32; i++) {
        prng_state[i] = buffer[outlen + i];
    }
}