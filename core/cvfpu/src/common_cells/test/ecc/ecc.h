#include <stdint.h>
#include <stdlib.h>

bool ispowerof2(unsigned int x);
void toBin(uint8_t *data, uint64_t word, size_t len);
void toByte(uint8_t *data, uint8_t *in_data, size_t len);
void printBits(const char *preamble, uint8_t *data, size_t len);
int calcParityLen(int data_bits);
void ecc_encode (uint64_t word, int d, uint8_t *codeword);
