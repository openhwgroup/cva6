#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   
   // ***************************** //
   // **** ADD YOUR CODE HERE ***** //
   // ***************************** //
   //
   // feel free to make a separate function for MI and MSI versions.
  int i, j, k, ii, jj, bsize;
  bsize = 16;
  for ( jj = bsize*coreid; jj < lda; jj += bsize*ncores) {
    for ( ii = 0; ii < lda; ii += bsize) {
      for ( j = jj; j < lda && j < jj + bsize; j++) {
	for ( i = ii; i < lda && i < ii + bsize; i += 8) {
	  data_t c1 = C[i + j*lda];
	  data_t c2 = C[i + j*lda + 1];
	  data_t c3 = C[i + j*lda + 2];
	  data_t c4 = C[i + j*lda + 3];
	  data_t c5 = C[i + j*lda + 4];
	  data_t c6 = C[i + j*lda + 5];
	  data_t c7 = C[i + j*lda + 6];
	  data_t c8 = C[i + j*lda + 7];
	  for ( k = 0; k < lda; k+=4 ) {
	    for (int x = 0; x < 4; x++) {
	      data_t a = A[j*lda + k+x];
	      data_t b1 = B[(k+x)*lda + i];
	      data_t b2 = B[(k+x)*lda + i + 1];
	      data_t b3 = B[(k+x)*lda + i + 2];
	      data_t b4 = B[(k+x)*lda + i + 3];
	      data_t b5 = B[(k+x)*lda + i + 4];
	      data_t b6 = B[(k+x)*lda + i + 5];
	      data_t b7 = B[(k+x)*lda + i + 6];
	      data_t b8 = B[(k+x)*lda + i + 7];
	      c1 += a * b1;
	      c2 += a * b2;
	      c3 += a * b3;
	      c4 += a * b4;
	      c5 += a * b5;
	      c6 += a * b6;
	      c7 += a * b7;
	      c8 += a * b8;
	    }
	  }
	  C[i + j*lda] = c1;
	  C[i + j*lda + 1] = c2;
	  C[i + j*lda + 2] = c3;
	  C[i + j*lda + 3] = c4;
	  C[i + j*lda + 4] = c5;
	  C[i + j*lda + 5] = c6;
	  C[i + j*lda + 6] = c7;
	  C[i + j*lda + 7] = c8;
	}
      }
    }
  }
  
}
