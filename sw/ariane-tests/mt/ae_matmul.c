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


 
	data_t *b1;
	data_t *b2;
	data_t *b3;
	data_t *b4;
	data_t c1;
	data_t c2;
	data_t c3;
	data_t c4;
	data_t a1;
	data_t a2;
	data_t a3;
	data_t a4;
	data_t a5;
	data_t a6;
	data_t a7;
	data_t a8;
	int i, j, k;
	static data_t BB[1024];



	//transpose B
		for ( k = 0; k < lda; k++) {
			for ( i = coreid*(lda/ncores); i < (coreid+1)*(lda/ncores); i++ )  {
				BB[i*lda + k] = B[k*lda + i];
			}
                  barrier(ncores);
		}

	for ( i = 0; i < lda; i+=4 ) {
		for ( j = coreid*(lda/ncores); j < (coreid+1)*(lda/ncores); j++ )  {
			c1 = 0; c2 = 0; c3 = 0; c4 = 0;
			b1 = &BB[(i+0)*lda];
			b2 = &BB[(i+1)*lda];
			b3 = &BB[(i+2)*lda];
			b4 = &BB[(i+3)*lda];
			for ( k = 0; k < lda; k+=8 ) { 

				a1 = A[j*lda + k+0];
				a2 = A[j*lda + k+1];
				a3 = A[j*lda + k+2];
				a4 = A[j*lda + k+3];
				a5 = A[j*lda + k+4];
				a6 = A[j*lda + k+5];
				a7 = A[j*lda + k+6];
				a8 = A[j*lda + k+7];

				c1 += a1 * b1[k+0];
				c1 += a2 * b1[k+1];
				c1 += a3 * b1[k+2];
				c1 += a4 * b1[k+3];
				c1 += a5 * b1[k+4];
				c1 += a6 * b1[k+5];
				c1 += a7 * b1[k+6];
				c1 += a8 * b1[k+7];

				c2 += a1 * b2[k+0];
				c2 += a2 * b2[k+1];
				c2 += a3 * b2[k+2];
				c2 += a4 * b2[k+3];
				c2 += a5 * b2[k+4];
				c2 += a6 * b2[k+5];
				c2 += a7 * b2[k+6];
				c2 += a8 * b2[k+7];

				c3 += a1 * b3[k+0];
				c3 += a2 * b3[k+1];
				c3 += a3 * b3[k+2];
				c3 += a4 * b3[k+3];
				c3 += a5 * b3[k+4];
				c3 += a6 * b3[k+5];
				c3 += a7 * b3[k+6];
				c3 += a8 * b3[k+7];

				c4 += a1 * b4[k+0];
				c4 += a2 * b4[k+1];
				c4 += a3 * b4[k+2];
				c4 += a4 * b4[k+3];
				c4 += a5 * b4[k+4];
				c4 += a6 * b4[k+5];
				c4 += a7 * b4[k+6];
				c4 += a8 * b4[k+7];


			}
			C[i+0 + j*lda] = c1;
			C[i+1 + j*lda] = c2;
			C[i+2 + j*lda] = c3;
			C[i+3 + j*lda] = c4;
                  barrier(ncores);
		}
	}

}
