#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   
   // ***************************** //
   // **** ADD YOUR CODE HERE ***** //
    int i, j, k, limit, end, kblock, iblock, r, jblock;
    int tempA1;
    int tempB1;

    limit = lda / ncores;
    j = (coreid)*limit;
    end = (coreid+1)*limit;
    
    kblock = 1;
    iblock = 1;
    jblock = 1;
   for (; j < end; j+= jblock)
      for ( k = 0; k < lda; k = k + kblock )  
      {
	  r = j*lda + k;
	  tempA1 = A[r];

        for ( i = 0; i < lda; i = i + iblock )  {
     	  tempB1 = k*lda + i;
	 
            C[i + j*lda] +=  tempA1*B[tempB1]; 

	 }
         barrier(ncores);
   }
   // ***************************** //
   //
   // feel free to make a separate function for MI and MSI versions.
 
}
