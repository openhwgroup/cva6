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
  int j2, i2, k2, j, i, k; 
  int tmpC00, tmpC01, tmpC02, tmpC03, tmpC04, tmpC05, tmpC06, tmpC07;
  int tmpC10, tmpC11, tmpC12, tmpC13, tmpC14, tmpC15, tmpC16, tmpC17;
  int jBLOCK = 32;
  int iBLOCK = 16;
  int kBLOCK = 32;
  static __thread int tB[4096]; //__thread
  int startInd = coreid*(lda/ncores);
  int endInd = (coreid+1)*(lda/ncores);

  //tranpose B (block?)
  for (i = 0; i < lda; i += 2) {
    for (j = startInd; j < endInd; j += 2) {
      tB[j*lda + i] = B[i*lda + j];
      tB[(j + 1)*lda + i] = B[i*lda + j + 1];
      tB[j*lda + i + 1] = B[(i + 1)*lda + j];
      tB[(j + 1)*lda + i + 1] = B[(i + 1)*lda + j + 1];
    }
    barrier(ncores);
  }

  // compute C[j*n + i] += A[j*n + k] + Btranspose[i*n + k]
  for ( j2 = 0; j2 < lda; j2 += jBLOCK )
    for ( i2 = startInd; i2 < endInd; i2 += iBLOCK )
      for ( j = j2; j < j2 + jBLOCK; j += 2 ) 
	for ( k2 = 0; k2 < lda; k2 += kBLOCK )
	  for ( i = i2; i < i2 + iBLOCK; i += 8) {
	    tmpC00 = C[j*lda + i + 0]; tmpC10 = C[(j + 1)*lda + i + 0];
	    tmpC01 = C[j*lda + i + 1]; tmpC11 = C[(j + 1)*lda + i + 1];
	    tmpC02 = C[j*lda + i + 2]; tmpC12 = C[(j + 1)*lda + i + 2];
	    tmpC03 = C[j*lda + i + 3]; tmpC13 = C[(j + 1)*lda + i + 3];
	    tmpC04 = C[j*lda + i + 4]; tmpC14 = C[(j + 1)*lda + i + 4];
	    tmpC05 = C[j*lda + i + 5]; tmpC15 = C[(j + 1)*lda + i + 5];
	    tmpC06 = C[j*lda + i + 6]; tmpC16 = C[(j + 1)*lda + i + 6];
	    tmpC07 = C[j*lda + i + 7]; tmpC17 = C[(j + 1)*lda + i + 7];
	    for ( k = k2; k < k2 + kBLOCK; k += 4) {
	      tmpC00 += A[j*lda + k] * tB[(i + 0)*lda + k]; 
	      tmpC01 += A[j*lda + k] * tB[(i + 1)*lda + k]; 
	      tmpC02 += A[j*lda + k] * tB[(i + 2)*lda + k]; 
	      tmpC03 += A[j*lda + k] * tB[(i + 3)*lda + k]; 
	      tmpC04 += A[j*lda + k] * tB[(i + 4)*lda + k]; 
	      tmpC05 += A[j*lda + k] * tB[(i + 5)*lda + k]; 
	      tmpC06 += A[j*lda + k] * tB[(i + 6)*lda + k]; 
	      tmpC07 += A[j*lda + k] * tB[(i + 7)*lda + k]; 
	      tmpC10 += A[(j + 1)*lda + k] * tB[(i + 0)*lda + k]; 
	      tmpC11 += A[(j + 1)*lda + k] * tB[(i + 1)*lda + k]; 
	      tmpC12 += A[(j + 1)*lda + k] * tB[(i + 2)*lda + k]; 
	      tmpC13 += A[(j + 1)*lda + k] * tB[(i + 3)*lda + k]; 
	      tmpC14 += A[(j + 1)*lda + k] * tB[(i + 4)*lda + k]; 
	      tmpC15 += A[(j + 1)*lda + k] * tB[(i + 5)*lda + k]; 
	      tmpC16 += A[(j + 1)*lda + k] * tB[(i + 6)*lda + k]; 
	      tmpC17 += A[(j + 1)*lda + k] * tB[(i + 7)*lda + k]; 

	      tmpC00 += A[j*lda + k + 1] * tB[(i + 0)*lda + k + 1];
	      tmpC01 += A[j*lda + k + 1] * tB[(i + 1)*lda + k + 1];
	      tmpC02 += A[j*lda + k + 1] * tB[(i + 2)*lda + k + 1];
	      tmpC03 += A[j*lda + k + 1] * tB[(i + 3)*lda + k + 1];
	      tmpC04 += A[j*lda + k + 1] * tB[(i + 4)*lda + k + 1];
	      tmpC05 += A[j*lda + k + 1] * tB[(i + 5)*lda + k + 1];
	      tmpC06 += A[j*lda + k + 1] * tB[(i + 6)*lda + k + 1];
	      tmpC07 += A[j*lda + k + 1] * tB[(i + 7)*lda + k + 1];
	      tmpC10 += A[(j + 1)*lda + k + 1] * tB[(i + 0)*lda + k + 1];
	      tmpC11 += A[(j + 1)*lda + k + 1] * tB[(i + 1)*lda + k + 1];
	      tmpC12 += A[(j + 1)*lda + k + 1] * tB[(i + 2)*lda + k + 1];
	      tmpC13 += A[(j + 1)*lda + k + 1] * tB[(i + 3)*lda + k + 1];
	      tmpC14 += A[(j + 1)*lda + k + 1] * tB[(i + 4)*lda + k + 1];
	      tmpC15 += A[(j + 1)*lda + k + 1] * tB[(i + 5)*lda + k + 1];
	      tmpC16 += A[(j + 1)*lda + k + 1] * tB[(i + 6)*lda + k + 1];
	      tmpC17 += A[(j + 1)*lda + k + 1] * tB[(i + 7)*lda + k + 1];

	      tmpC00 += A[j*lda + k + 2] * tB[(i + 0)*lda + k + 2]; 
	      tmpC01 += A[j*lda + k + 2] * tB[(i + 1)*lda + k + 2]; 
	      tmpC02 += A[j*lda + k + 2] * tB[(i + 2)*lda + k + 2]; 
	      tmpC03 += A[j*lda + k + 2] * tB[(i + 3)*lda + k + 2]; 
	      tmpC04 += A[j*lda + k + 2] * tB[(i + 4)*lda + k + 2]; 
	      tmpC05 += A[j*lda + k + 2] * tB[(i + 5)*lda + k + 2]; 
	      tmpC06 += A[j*lda + k + 2] * tB[(i + 6)*lda + k + 2]; 
	      tmpC07 += A[j*lda + k + 2] * tB[(i + 7)*lda + k + 2]; 
	      tmpC10 += A[(j + 1)*lda + k + 2] * tB[(i + 0)*lda + k + 2]; 
	      tmpC11 += A[(j + 1)*lda + k + 2] * tB[(i + 1)*lda + k + 2]; 
	      tmpC12 += A[(j + 1)*lda + k + 2] * tB[(i + 2)*lda + k + 2]; 
	      tmpC13 += A[(j + 1)*lda + k + 2] * tB[(i + 3)*lda + k + 2]; 
	      tmpC14 += A[(j + 1)*lda + k + 2] * tB[(i + 4)*lda + k + 2]; 
	      tmpC15 += A[(j + 1)*lda + k + 2] * tB[(i + 5)*lda + k + 2]; 
	      tmpC16 += A[(j + 1)*lda + k + 2] * tB[(i + 6)*lda + k + 2]; 
	      tmpC17 += A[(j + 1)*lda + k + 2] * tB[(i + 7)*lda + k + 2]; 

	      tmpC00 += A[j*lda + k + 3] * tB[(i + 0)*lda + k + 3];
	      tmpC01 += A[j*lda + k + 3] * tB[(i + 1)*lda + k + 3];
	      tmpC02 += A[j*lda + k + 3] * tB[(i + 2)*lda + k + 3];
	      tmpC03 += A[j*lda + k + 3] * tB[(i + 3)*lda + k + 3];
	      tmpC04 += A[j*lda + k + 3] * tB[(i + 4)*lda + k + 3];
	      tmpC05 += A[j*lda + k + 3] * tB[(i + 5)*lda + k + 3];
	      tmpC06 += A[j*lda + k + 3] * tB[(i + 6)*lda + k + 3];
	      tmpC07 += A[j*lda + k + 3] * tB[(i + 7)*lda + k + 3]; 
	      tmpC10 += A[(j + 1)*lda + k + 3] * tB[(i + 0)*lda + k + 3];
	      tmpC11 += A[(j + 1)*lda + k + 3] * tB[(i + 1)*lda + k + 3];
	      tmpC12 += A[(j + 1)*lda + k + 3] * tB[(i + 2)*lda + k + 3];
	      tmpC13 += A[(j + 1)*lda + k + 3] * tB[(i + 3)*lda + k + 3];
	      tmpC14 += A[(j + 1)*lda + k + 3] * tB[(i + 4)*lda + k + 3];
	      tmpC15 += A[(j + 1)*lda + k + 3] * tB[(i + 5)*lda + k + 3];
	      tmpC16 += A[(j + 1)*lda + k + 3] * tB[(i + 6)*lda + k + 3];
	      tmpC17 += A[(j + 1)*lda + k + 3] * tB[(i + 7)*lda + k + 3];
	    }
	    C[j*lda + i + 0] = tmpC00; C[(j + 1)*lda + i + 0] = tmpC10; 
	    C[j*lda + i + 1] = tmpC01; C[(j + 1)*lda + i + 1] = tmpC11; 
	    C[j*lda + i + 2] = tmpC02; C[(j + 1)*lda + i + 2] = tmpC12; 
	    C[j*lda + i + 3] = tmpC03; C[(j + 1)*lda + i + 3] = tmpC13; 
	    C[j*lda + i + 4] = tmpC04; C[(j + 1)*lda + i + 4] = tmpC14; 
	    C[j*lda + i + 5] = tmpC05; C[(j + 1)*lda + i + 5] = tmpC15; 
	    C[j*lda + i + 6] = tmpC06; C[(j + 1)*lda + i + 6] = tmpC16; 
	    C[j*lda + i + 7] = tmpC07; C[(j + 1)*lda + i + 7] = tmpC17; 
            barrier(ncores);
	  }
}
