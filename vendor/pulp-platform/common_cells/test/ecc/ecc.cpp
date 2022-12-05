// SPDX-License-Identifier: Apache-2.0
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

#include "ecc.h"

#include <stdint.h>
#include <stdlib.h>
#include <math.h>
#include <stdio.h>

bool ispowerof2(unsigned int x) {
    return x && !(x & (x - 1));
}

void toBin(uint8_t *data, uint64_t word, size_t len) {
    for (int i = 0; i < len; i++){
        data[i] = (word >> i) & 0x1;
    }
}

void toByte(uint8_t *data, uint8_t *in_data, size_t len) {
    for (int j = len; j >= 0; j -= 8) {
        if (j >= len) {
        } else {
            // split up in single bytes
            uint8_t byte = 0;
            for (int i = 0; i < 8; i++)
                byte += in_data[j + i] << i;

            data[(j/8)] = byte;
            // printf("%02x", byte);
        }
    }
}

void printBits(const char *preamble, uint8_t *data, size_t len) {
#ifdef DEBUG
    printf("%s", preamble);
    for (int j = 0; j < len; j++) printf("%1d", data[j]);
    printf("\n");
#endif
}

int calcParityLen(int data_bits) {
    int cw_width = 2;
    while (pow(2, cw_width) < cw_width + data_bits + 1) cw_width++;
    return cw_width;
}

void ecc_encode (uint64_t word, int d, uint8_t *codeword) {
    uint8_t info [d];
    uint8_t parity [d];
    int p = calcParityLen(d);

#ifdef DEBUG
    printf("Data Bits: %d\nParity Bits: %d\n", d, p);
#endif

    toBin(info, word, d);
    printBits("information bits = ", info, d);

    for (int i = 1, idx = 0; i <= d + p; i++) {
        codeword[i - 1] = (ispowerof2(i)) ? 0 : info[idx++];
    }

    printBits("expanded codeword = ", codeword, d + p);

    for (int i = 0; i < p; i++) {
        int parity = 0;

        for (int k = 1; k <= d + p; k++) {
            if (k & (1 << i))
                parity ^= codeword[k - 1];
        }
#ifdef DEBUG
        printf("Parity: %d %d\n", i, parity);
#endif
        codeword[(1 << i) - 1] = parity;
    }

    codeword[d + p] = 0;
    for (int i = 0; i < d + p; i++) codeword[d + p] ^= codeword[i];

#ifdef DEBUG
    printf("Parity: %d %d\n", p, codeword[d + p]);
#endif

    printBits("codeword = ", codeword, d + p + 1);

    // Convert to hex
    printf("gm = ");
    for (int j = d + p + 1; j >= 0; j -= 8) {
        if (j >= d + p + 1) {
        } else {
            // split up in single bytes
            uint8_t byte = 0;
            for (int i = 0; i < 8; i++)
                byte += codeword[j + i] << i;
            printf("%02x", byte);
        }
    }
    printf("\n");
}
