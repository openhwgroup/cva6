#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
  int i, j, k;

  for (i = 0; i < lda; i += 2) {
    for (j = coreid * (lda / ncores); j < (coreid + 1) * (lda / ncores); j += 4) {
      register data_t c00 = 0, c01 = 0;
      register data_t c10 = 0, c11 = 0;
      register data_t c20 = 0, c21 = 0;
      register data_t c30 = 0, c31 = 0;

      register data_t a0, a1, a2, a3, b0, b1;
      for (k = 0; k < lda; k++) {
        a0 = A[j*lda + k + 0*lda];
        a1 = A[j*lda + k + 1*lda];
        a2 = A[j*lda + k + 2*lda];
        a3 = A[j*lda + k + 3*lda];

        b0 = B[k*lda + i + 0];
        b1 = B[k*lda + i + 1];

        c00 += a0 * b0; c01 += a0 * b1;
        c10 += a1 * b0; c11 += a1 * b1;
        c20 += a2 * b0; c21 += a2 * b1;
        c30 += a3 * b0; c31 += a3 * b1;
      }

      C[i + j*lda + 0 + 0*lda] = c00; C[i + j*lda + 1 + 0*lda] = c01;
      C[i + j*lda + 0 + 1*lda] = c10; C[i + j*lda + 1 + 1*lda] = c11;
      C[i + j*lda + 0 + 2*lda] = c20; C[i + j*lda + 1 + 2*lda] = c21;
      C[i + j*lda + 0 + 3*lda] = c30; C[i + j*lda + 1 + 3*lda] = c31;
    }
  }
}
