// See LICENSE for license details.

#ifndef _MM_H
#define _MM_H

#include <string.h>
#include <stdint.h>
#include <math.h>

#ifdef SP
typedef float t;
#define fma fmaf
#else
typedef double t;
#endif

#define inline inline __attribute__((always_inline))

#define alloca_aligned(s, a) ((void*)(((uintptr_t)alloca((s)+(a)-1)+(a)-1)&~((a)-1)))

#include "rb.h"

#ifdef __cplusplus
extern "C" {
#endif

void mm(size_t m, size_t n, size_t p,
        t* a, size_t lda, t* b, size_t ldb, t* c, size_t ldc);

#ifdef __cplusplus
}
#endif

//void rb(t* a, t* b, t* c, size_t lda, size_t ldb, size_t ldc);

#endif
