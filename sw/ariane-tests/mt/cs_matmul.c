#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   int i, j, k, n, m, c1, c2;
   for ( j = coreid; j < lda; j += 2*ncores ) {
      for ( i = 0; i < lda; i += 1 ){
         c1 = 0;     //global vars c1, c2
         c2 = 0;
         for ( k = 0; k < lda; k += 1 ) {
            c1 += A[j * lda + k] * B[k*lda + i];
            c2 += A[(j+ncores) * lda + k] * B[k*lda + i];
         }

         C[i + j * lda] = c1;
         C[i + (j+ncores) * lda] = c2;
         barrier(ncores);
      }
   }
   
}
