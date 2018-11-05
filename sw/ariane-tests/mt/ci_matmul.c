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
   
//----------MSI--------------
/*
   int i,j,k;
   barrier(nc);
   for(j = coreid*lda/ncores; j < coreid*lda/ncores + lda/ncores; j++) {
	for(i = 0; i < lda; i+=4) {
		data_t Cval0 = 0;
		data_t Cval1 = 0;
		data_t Cval2 = 0;
		data_t Cval3 = 0;
		for(k = 0; k < lda; k++) {
			Cval0 += A[j*lda+k]*B[k*lda+i];
			Cval1 += A[j*lda+k]*B[k*lda+i+1];
			Cval2 += A[j*lda+k]*B[k*lda+i+2];
			Cval3 += A[j*lda+k]*B[k*lda+i+3];
		}
		C[j*lda+i] = Cval0;
		C[j*lda+i+1] = Cval1;
		C[j*lda+i+2] = Cval2;
		C[j*lda+i+3] = Cval3;
	}
   }
*/

//------------------MI-------------------

   int i,j,k;
   barrier(ncores);
   for(j = coreid*lda/ncores; j < coreid*lda/ncores + lda/ncores; j++) {
        for(i = 0; i < lda; i+=4) {
		data_t Cval0 = 0;
	        data_t Cval1 = 0;
        	data_t Cval2 = 0;
		data_t Cval3 = 0;
		if(coreid == 0) {
	               	for(k = 0; k < lda; k++) {
        	              	Cval0 += A[j*lda+k]*B[k*lda+i];
				Cval1 += A[j*lda+k]*B[k*lda+i+1];
				Cval2 += A[j*lda+k]*B[k*lda+i+2];
				Cval3 += A[j*lda+k]*B[k*lda+i+3];
			}
		} else {
			for(k = lda-1; k >= 0; k--) {
                                Cval0 += A[j*lda+k]*B[k*lda+i];
	                        Cval1 += A[j*lda+k]*B[k*lda+i+1];
                                Cval2 += A[j*lda+k]*B[k*lda+i+2];
                                Cval3 += A[j*lda+k]*B[k*lda+i+3];
                        }
		}
		C[j*lda+i] = Cval0;
                C[j*lda+i+1] = Cval1;
                C[j*lda+i+2] = Cval2;
                C[j*lda+i+3] = Cval3;
	}
   }
}
