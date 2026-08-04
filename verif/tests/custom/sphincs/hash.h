#ifndef SPX_HASH_H
#define SPX_HASH_H

#include <stdint.h>

void initialize_hash_function(const unsigned char *pub_seed,
                              const unsigned char *sk_seed);

void prf_addr(unsigned char *out, const unsigned char *key,
              const uint32_t addr[8]);

void gen_message_random(unsigned char *R, const unsigned char *sk_seed,
                        const unsigned char *optrand,
                        const unsigned char *m, unsigned long long mlen);

void hash_message(unsigned char *digest, uint64_t *tree, uint32_t *leaf_idx,
                  const unsigned char *R, const unsigned char *pk,
                  const unsigned char *m, unsigned long long mlen);

#endif
