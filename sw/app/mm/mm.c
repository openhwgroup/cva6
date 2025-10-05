// See LICENSE for license details.

#include "common.h"
#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <alloca.h>

#define MIN(a, b) ((a) < (b) ? (a) : (b))

static void mm_naive(size_t m, size_t n, size_t p,
                            t* a, size_t lda, t* b, size_t ldb, t* c, size_t ldc)
{
  for (size_t i = 0; i < m; i++)
  {
    for (size_t j = 0; j < n; j++)
    {
      t s0 = c[i*ldc+j], s1 = 0, s2 = 0, s3 = 0;
      for (size_t k = 0; k < p/4*4; k+=4)
      {
        s0 = fma(a[i*lda+k+0], b[(k+0)*ldb+j], s0);
        s1 = fma(a[i*lda+k+1], b[(k+1)*ldb+j], s1);
        s2 = fma(a[i*lda+k+2], b[(k+2)*ldb+j], s2);
        s3 = fma(a[i*lda+k+3], b[(k+3)*ldb+j], s3);
      }
      for (size_t k = p/4*4; k < p; k++)
        s0 = fma(a[i*lda+k], b[k*ldb+j], s0);
      c[i*ldc+j] = (s0 + s1) + (s2 + s3);
    }
  }
}

static inline void mm_rb(size_t m, size_t n, size_t p,
                         t* a, size_t lda, t* b, size_t ldb, t* c, size_t ldc)
{
  size_t mb = m/RBM*RBM, nb = n/RBN*RBN;
  for (size_t i = 0; i < mb; i += RBM)
  {
    for (size_t j = 0; j < nb; j += RBN)
      kloop(p, a+i*lda, lda, b+j, ldb, c+i*ldc+j, ldc);
    mm_naive(RBM, n - nb, p, a+i*lda, lda, b+nb, ldb, c+i*ldc+nb, ldc);
  }
  mm_naive(m - mb, n, p, a+mb*lda, lda, b, ldb, c+mb*ldc, ldc);
}

static inline void repack(t* a, size_t lda, const t* a0, size_t lda0, size_t m, size_t p)
{
  for (size_t i = 0; i < m; i++)
  {
    for (size_t j = 0; j < p/8*8; j+=8)
    {
      t t0 = a0[i*lda0+j+0];
      t t1 = a0[i*lda0+j+1];
      t t2 = a0[i*lda0+j+2];
      t t3 = a0[i*lda0+j+3];
      t t4 = a0[i*lda0+j+4];
      t t5 = a0[i*lda0+j+5];
      t t6 = a0[i*lda0+j+6];
      t t7 = a0[i*lda0+j+7];
      a[i*lda+j+0] = t0;
      a[i*lda+j+1] = t1;
      a[i*lda+j+2] = t2;
      a[i*lda+j+3] = t3;
      a[i*lda+j+4] = t4;
      a[i*lda+j+5] = t5;
      a[i*lda+j+6] = t6;
      a[i*lda+j+7] = t7;
    }
    for (size_t j = p/8*8; j < p; j++)
      a[i*lda+j] = a0[i*lda0+j];
  }
}

static void mm_cb(size_t m, size_t n, size_t p,
                  t* a, size_t lda, t* b, size_t ldb, t* c, size_t ldc)
{
  size_t nmb = m/CBM, nnb = n/CBN, npb = p/CBK;
  size_t mb = nmb*CBM, nb = nnb*CBN, pb = npb*CBK;
  //t a1[mb*pb], b1[pb*nb], c1[mb*nb];
  t* a1 = (t*)alloca_aligned(sizeof(t)*mb*pb, 8192);
  t* b1 = (t*)alloca_aligned(sizeof(t)*pb*nb, 8192);
  t* c1 = (t*)alloca_aligned(sizeof(t)*mb*nb, 8192);

    for (size_t i = 0; i < mb; i += CBM)
      for (size_t j = 0; j < pb; j += CBK)
        repack(a1 + (npb*(i/CBM) + j/CBK)*(CBM*CBK), CBK, a + i*lda + j, lda, CBM, CBK);

  for (size_t i = 0; i < pb; i += CBK)
    for (size_t j = 0; j < nb; j += CBN)
      repack(b1 + (nnb*(i/CBK) + j/CBN)*(CBK*CBN), CBN, b + i*ldb + j, ldb, CBK, CBN);

    for (size_t i = 0; i < mb; i += CBM)
      for (size_t j = 0; j < nb; j += CBN)
        repack(c1 + (nnb*(i/CBM) + j/CBN)*(CBM*CBN), CBN, c + i*ldc + j, ldc, CBM, CBN);

  for (size_t i = 0; i < mb; i += CBM)
  {
    for (size_t j = 0; j < nb; j += CBN)
    {
      for (size_t k = 0; k < pb; k += CBK)
      {
        mm_rb(CBM, CBN, CBK,
              a1 + (npb*(i/CBM) + k/CBK)*(CBM*CBK), CBK,
              b1 + (nnb*(k/CBK) + j/CBN)*(CBK*CBN), CBN,
              c1 + (nnb*(i/CBM) + j/CBN)*(CBM*CBN), CBN);
      }
      if (pb < p)
      {
        mm_rb(CBM, CBN, p - pb,
              a + i*lda + pb, lda,
              b + pb*ldb + j, ldb,
              c1 + (nnb*(i/CBM) + j/CBN)*(CBM*CBN), CBN);
      }
    }
    if (nb < n)
    {
      for (size_t k = 0; k < p; k += CBK)
      {
        mm_rb(CBM, n - nb, MIN(p - k, CBK),
              a + i*lda + k, lda,
              b + k*ldb + nb, ldb,
              c + i*ldc + nb, ldc);
      }
    }
  }
  if (mb < m)
  {
    for (size_t j = 0; j < n; j += CBN)
    {
      for (size_t k = 0; k < p; k += CBK)
      {
        mm_rb(m - mb, MIN(n - j, CBN), MIN(p - k, CBK),
              a + mb*lda + k, lda,
              b + k*ldb + j, ldb,
              c + mb*ldc + j, ldc);
      }
    }
  }

    for (size_t i = 0; i < mb; i += CBM)
      for (size_t j = 0; j < nb; j += CBN)
        repack(c + i*ldc + j, ldc, c1 + (nnb*(i/CBM) + j/CBN)*(CBM*CBN), CBN, CBM, CBN);
}

void mm(size_t m, size_t n, size_t p,
        t* a, size_t lda, t* b, size_t ldb, t* c, size_t ldc)
{
  if (__builtin_expect(m <= 2*CBM && n <= 2*CBN && p <= 2*CBK, 1))
    mm_rb(m, n, p, a, lda, b, ldb, c, ldc);
  else
    mm_cb(m, n, p, a, lda, b, ldb, c, ldc);
}
