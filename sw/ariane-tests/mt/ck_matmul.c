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
  int i, j, k, ii, jj, bsize, start;
  bsize = 16;
  start = bsize*coreid;
  for ( jj = start; jj < lda; jj += bsize*ncores) {
    int first = 1;
    for ( ii = start; ii !=start || first; ii=(bsize+ii) % lda) {
      first = 0;
      for ( j = jj; j < lda && j < jj + bsize; j+=4) {
	for ( i = ii; i < lda && i < ii + bsize; i+=2) {
	  data_t c1 = C[i + j*lda];
	  data_t c2 = C[i + j*lda + 1];
	  data_t c3 = C[i + (j+1)*lda];
	  data_t c4 = C[i + (j+1)*lda + 1];
	  data_t c5 = C[i + (j+2)*lda];
	  data_t c6 = C[i + (j+2)*lda + 1];
	  data_t c7 = C[i + (j+3)*lda];
	  data_t c8 = C[i + (j+3)*lda + 1];
	  for ( k = 0; k < lda; k+=8){
	    for (int x = 0; x < 8; x++) {
	    data_t a = A[j*lda + k+x];
	    data_t a1 = A[(j+1)*lda +k+x];
	    data_t a2 = A[(j+2)*lda +k+x];
	    data_t a3 = A[(j+3)*lda +k+x];
	    data_t b1 = B[(k+x)*lda + i];
	    data_t b2 = B[(k+x)*lda + i + 1];
	    c1 += a * b1;
	    c2 += a * b2;
	    c3 += a1* b1;
	    c4 += a1* b2;
	    c5 += a2* b1;
	    c6 += a2* b2;
	    c7 += a3* b1;
	    c8 += a3* b2;
	    }
	  }
	  C[i + j*lda] = c1;
	  C[i + j*lda + 1] = c2;
	  C[i + (j+1)*lda] = c3;
	  C[i + (j+1)*lda + 1] = c4;
	  C[i + (j+2)*lda] = c5;
	  C[i + (j+2)*lda + 1] = c6;
	  C[i + (j+3)*lda] = c7;
	  C[i + (j+3)*lda + 1] = c8;
	}
      }
   }
  }
}
