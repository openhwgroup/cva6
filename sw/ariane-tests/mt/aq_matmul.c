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
   
   	for (int  i = coreid; i < lda; i+=ncores*2)
       	{
		for (int j = 0; j < lda; j++)
       		{	
         		for (int k = 0; k < lda; k++)
	 		{	 
	    			int A12 = A[j*lda + k];
	    			int B1 = B[k*lda + i];
            			int B2 = B[k*lda + i + ncores];
	    			C[i+j*lda] += A12 * B1;
	    			C[i+ncores+j*lda] += A12 * B2;
	   		 	//C[i+j*lda] += A[j*lda +k] * B[k*lda +i];
	 		}
       		}
	}
}
