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
   
   int i, j, k, B_t[32*32], x, y;
   int ALoc, BLoc, CLoc;
//   int ii = 0, done = 0;
   //for(x = coreid*(lda/ncores); x < (coreid+1)*(lda/ncores) && x < lda; x++) {
   for (x = 0; x < lda; x++) {
   		for(y = 0; y < lda; y++) {
   			B_t[y*lda + x] = B[x*lda + y];
   		}
   }
  // for ( ii = lda/4 ; ii < lda ; ii += lda/4)
   //{
//   	   for ( i = coreid*(ii/ncores); i < (coreid+1)*(ii/ncores) && i < ii; i++ )
	   for ( i = coreid*(lda/ncores); i < (coreid+1)*(lda/ncores) && i < lda; i++ )
	   {
   		  ALoc = i*lda;
    	  for ( j = 0; j < lda; j++ ) 
	      {
	      	 BLoc = j*lda;
      		 CLoc = i*lda + j;
    	     for ( k = 0; k < lda; k++ ) 
	         {
            	C[CLoc] += A[ALoc + k] * B_t[BLoc + k];
        	 }
    	  }
	   }
   //}
}
