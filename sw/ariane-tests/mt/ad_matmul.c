#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   int i, k;
   int j = coreid*(lda/ncores);
   int jend = (coreid+1)*(lda/ncores);
   for ( ; j < jend; j++ )
   {
      int j32 = j << 5;
      data_t* Cj32 = C + j32;
      for ( k = 0; k < 32; k+=2 )
      {
	 data_t Aj32k  = A[k + j32];
	 data_t Aj32k2 = A[k + 1 + j32];
	 data_t* Bk32  = B + (k << 5);
	 data_t* Bk322 = Bk32 + 32;
	 for ( i = 0; i < 32; i+=4 )
	 {
            Cj32[i]   += Aj32k  * Bk32   [i];
            Cj32[i]   += Aj32k2 * Bk322  [i];
            Cj32[i+1] += Aj32k  * Bk32 [i+1];
            Cj32[i+1] += Aj32k2 * Bk322[i+1];
            Cj32[i+2] += Aj32k  * Bk32 [i+2];
            Cj32[i+2] += Aj32k2 * Bk322[i+2];
            Cj32[i+3] += Aj32k  * Bk32 [i+3];
            Cj32[i+3] += Aj32k2 * Bk322[i+3];
	 }
         barrier(ncores);
      }
   }
   
 
}
