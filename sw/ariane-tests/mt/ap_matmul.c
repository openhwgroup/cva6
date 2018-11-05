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
   int i, j, k, ii, jj, kk;
   int block = lda / ncores;
   int leftover = lda % ncores;
   int start = block * coreid;


 
   for ( j = start; j < (start+block); j++ )
      for ( k = 0; k < lda; k++ )  
      {
         for ( i = 0; i < lda; i++ ) 
         {
            C[i + j*lda] += A[j*lda + k] * B[k*lda + i];
         }
      }
}
