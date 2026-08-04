#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

#include "../api.h"
#include "../params.h"
#include "../randombytes.h"
#include "test_print.h"
#include "test_syscalls.h"

#define SPX_MLEN 32
#define SPX_SIGNATURES 1

int main()
{
    int ret = 0;
    int i;

    unsigned char pk[SPX_PK_BYTES];
    unsigned char sk[SPX_SK_BYTES];
    unsigned char m[SPX_MLEN];
    unsigned char sm[SPX_BYTES + SPX_MLEN];
    unsigned char mout[SPX_BYTES + SPX_MLEN];
    unsigned long long smlen;
    unsigned long long mlen;
#ifdef PRINT_CYCLES
    uint32_t start_cycles;
    uint32_t end_cycles;
#endif

    randombytes(m, SPX_MLEN);

    print_str("Generating keypair...\n");
#ifdef PRINT_CYCLES
    start_cycles = get_cycles();
#endif
    int r_keypair = crypto_sign_keypair(pk, sk);
#ifdef PRINT_CYCLES
    end_cycles = get_cycles();
    print_str("Keypair generation cycle count: ");
    print_int(end_cycles - start_cycles);
    print_str("\n");
#endif

    if (r_keypair) {
        print_str("Keypair generation failed!\n");
        return -1;
    }
    print_str("Keypair generation successful.\n");

    print_str("Testing ");
    print_int(SPX_SIGNATURES);
    print_str(" signatures.. \n");

    for (i = 0; i < SPX_SIGNATURES; i++) {
        printf("  - iteration #%d:\n", i);
        print_str("  - iteration #");
        print_int(i);
        print_str(":\n");

        print_str("Signing message...");
#ifdef PRINT_CYCLES
        start_cycles = get_cycles();
#endif
        crypto_sign(sm, &smlen, m, SPX_MLEN, sk);
#ifdef PRINT_CYCLES
        end_cycles = get_cycles();
        print_str("Signature generation cycle count: ");
        print_int(end_cycles - start_cycles);
        print_str("\n");
#endif

        if (smlen != SPX_BYTES + SPX_MLEN) {
            print_str("smlen incorrect\n");
            ret = -1;
        }
        else {
            print_str("smlen as expected.\n");
        }

        /* Test if signature is valid. */
        print_str("Verifying message...\n");
#ifdef PRINT_CYCLES
        start_cycles = get_cycles();
#endif
        int r_sign_open = crypto_sign_open(mout, &mlen, sm, smlen, pk);
#ifdef PRINT_CYCLES
        end_cycles = get_cycles();
        print_str("Signature verification cycle count: ");
        print_int(end_cycles - start_cycles);
        print_str("\n");
#endif
        if (r_sign_open) {
            print_str("Verification failed!\n");
            ret = -1;
        }
        else {
            print_str("Verification succeeded.\n");
        }

        /* Test if the correct message was recovered. */
        if (mlen != SPX_MLEN) {
            print_str("mlen incorrect!\n");
            ret = -1;
        }
        else {
            printf("mlen as expected.\n");
        }
        if (memcmp(m, mout, SPX_MLEN)) {
            print_str("Output message incorrect!\n");
            ret = -1;
        }
        else {
            print_str("Output message as expected.\n");
        }

        /* Test if signature is valid when validating in-place. */
        if (crypto_sign_open(sm, &mlen, sm, smlen, pk)) {
            print_str("In-place verification failed!\n");
            ret = -1;
        }
        else {
            print_str("In-place verification succeeded.\n");
        }

        /* Test if flipping bits invalidates the signature (it should). */

        /* Flip the first bit of the message. Should invalidate. */
        sm[smlen - 1] ^= 1;
        if (!crypto_sign_open(mout, &mlen, sm, smlen, pk)) {
            print_str("Flipping a bit of m DID NOT invalidate signature!\n");
            ret = -1;
        }
        else {
            print_str("Flipping a bit of m invalidates signature.\n");
        }
        sm[smlen - 1] ^= 1;

#ifdef SPX_TEST_INVALIDSIG
        int j;
        /* Flip one bit per hash; the signature is entirely hashes. */
        for (j = 0; j < (int)(smlen - SPX_MLEN); j += SPX_N) {
            sm[j] ^= 1;
            if (!crypto_sign_open(mout, &mlen, sm, smlen, pk)) {
                print_str("Flipping bit ");
                print_int(j);
                print_str(" DID NOT invalidate sig + m!\n");
                sm[j] ^= 1;
                ret = -1;
                break;
            }
            sm[j] ^= 1;
        }
        if (j >= (int)(smlen - SPX_MLEN)) {
            print_str("Changing any signature hash invalidates signature.\n");
        }
#endif
    }

    return ret;
}
