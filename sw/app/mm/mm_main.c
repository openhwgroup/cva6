// See LICENSE for license details.

#include "common.h"
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"

#pragma GCC optimize ("unroll-loops")

void thread_entry(int cid, int nc)
{
  const int R = 8;
  int m, n, p;
  uint64_t s = 0xdeadbeefU;
  
  m = CBM;
  n = CBN;
  p = CBK;

  t a[m*p];
  t b[p*n];
  t c[m*n];

  for (size_t i = 0; i < m; i++)
    for (size_t j = 0; j < p; j++)
      a[i*p+j] = (t)(s = lfsr(s));
  for (size_t i = 0; i < p; i++)
    for (size_t j = 0; j < n; j++)
      b[i*n+j] = (t)(s = lfsr(s));
  memset(c, 0, m*n*sizeof(c[0]));

  size_t instret, cycles;
  for (int i = 0; i < R; i++)
  {
    instret = -read_csr(minstret);
    cycles = -read_csr(mcycle);
    mm(m, n, p, a, p, b, n, c, n);
    instret += read_csr(minstret);
    cycles += read_csr(mcycle);
  }

  asm volatile("fence");

  printf("C%d: reg block %dx%dx%d, cache block %dx%dx%d\n",
         cid, RBM, RBN, RBK, CBM, CBN, CBK);
  printf("C%d: %d instructions\n", cid, (int)(instret));
  printf("C%d: %d cycles\n", cid, (int)(cycles));
  printf("C%d: %d flops\n", cid, 2*m*n*p);
  printf("C%d: %d Mflops @ 1 GHz\n", cid, 2000*m*n*p/(cycles));

#if 1
  for (size_t i = 0; i < m; i++)
  {
    for (size_t j = 0; j < n; j++)
    {
      t s = 0;
      for (size_t k = 0; k < p; k++)
        s += a[i*p+k] * b[k*n+j];
      s *= R;
      if (fabs(c[i*n+j]-s) > fabs(1e-6*s))
      {
        printf("C%d: c[%lu][%lu] %f != %f\n", cid, i, j, c[i*n+j], s);
        exit(1);
      }
    }
  }
#endif

  barrier(nc);
  exit(0);
}
