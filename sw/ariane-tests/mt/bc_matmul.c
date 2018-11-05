#include "stdlib.h"

#include "util.h"

#include "dataset.h"

#define REG_I 8
#define REG_J 2
//#define BLOCK_I 32
#define BLOCK_J 16
#define BLOCK_K 16
#define LDA 32
#define NCORES 2
#define MIN(X,Y) (X < Y ? X : Y)

void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   
   // ***************************** //
   // **** ADD YOUR CODE HERE ***** //
   // ***************************** //
   //
   // feel free to make a separate function for MI and MSI versions.

  int i, j, k, ri, rj, ii, jj, kk;
  data_t *Aj, *Cj, *Bi;
  data_t c[REG_I][REG_J], a[REG_J], b[REG_I];
  size_t start = coreid * (LDA / NCORES), end = (coreid == NCORES - 1 ? LDA : (coreid + 1) * (LDA / NCORES));
     
  /* if (coreid > 0) { */
  /*   return; */
  /* } */
  /* start = 0, end = lda; */
  if (ncores == NCORES && lda == LDA) {
    for (jj = start; jj < end; jj += BLOCK_J)
      for (kk = 0; kk < LDA; kk += BLOCK_K)
	//for (ii = 0; ii < LDA; ii += BLOCK_I)
	for (j = jj; j < MIN(end, jj + BLOCK_J); j += REG_J) {
	  Aj = A + j*LDA;
	  Cj = C + j*LDA;
	  for (i = 0; i < LDA; i += REG_I) {
	    /* Load C in register blocks. */
	    Bi = B + i;
	    for (ri = 0; ri < REG_I; ri++) {
	      for (rj = 0; rj < REG_J; rj++) {
		c[ri][rj] = Cj[i + ri + ( rj)*LDA];
	      }
	    }
	    
	    
	    for (k = kk; k < MIN(LDA, kk + BLOCK_K); k++) {
	      /* Load a,b in register blocks. */
	      /*	  for (rj = 0; rj < REG_J; rj++) {
			  a[rj] = A[(j + rj)*LDA + k];
			  }*/
	      /* for (ri = 0; ri < REG_I; ri++) { */
	      /* 	b[ri] = Bi[k*LDA  + ri]; */
	      /* } */
	      /* /\* Compute C in register blocks. *\/ */
	      /* for (rj = 0; rj < REG_J; rj++) { */
	      /* 	a[rj] = Aj[( rj)*LDA + k]; */
	      /* 	for (ri = 0; ri < REG_I; ri++) { */
	      /* 	  c[ri][rj] += a[rj] * b[ri]; */
	      /* 	} */
	      /* } */
	      a[0] = Aj[k];
	      a[1] = Aj[k + LDA];
	      b[0] = Bi[k*LDA];
	      b[1] = Bi[k*LDA + 1];
	      b[2] = Bi[k*LDA + 2];
	      b[3] = Bi[k*LDA + 3];
	      b[4] = Bi[k*LDA + 4];
	      b[5] = Bi[k*LDA + 5];
	      b[6] = Bi[k*LDA + 6];
	      b[7] = Bi[k*LDA + 7];

	      
	      c[0][0] += b[0] * a[0];
	      c[0][1] += b[0] * a[1];
	      c[1][0] += b[1] * a[0];
	      c[1][1] += b[1] * a[1];
	      c[2][0] += b[2] * a[0];
	      c[2][1] += b[2] * a[1];
	      c[3][0] += b[3] * a[0];
	      c[3][1] += b[3] * a[1];
	      c[4][0] += b[4] * a[0];
	      c[4][1] += b[4] * a[1];
	      c[5][0] += b[5] * a[0];
	      c[5][1] += b[5] * a[1];
	      c[6][0] += b[6] * a[0];
	      c[6][1] += b[6] * a[1];
	      c[7][0] += b[7] * a[0];
	      c[7][1] += b[7] * a[1];
	      

	      /* c[0][0] +=  b[0] * a[0];	       */
	      /* c[1][1] +=  b[1] * a[1];              */
	      /* c[2][0] +=  b[2] * a[0];	       */
	      /* c[3][1] +=  b[3] * a[1];	       */
	      /* c[4][0] +=  b[4] * a[0];	       */
	      /* c[5][1] +=  b[5] * a[1];	       */
	      /* c[6][0] +=  b[6] * a[0];	       */
	      /* c[7][1] +=  b[7] * a[1];	       */
	      /* c[0][0] +=  b[0] * a[0];	       */
	      /* c[1][1] +=  b[1] * a[1];	       */
	      /* c[2][0] +=  b[2] * a[0];	       */
	      /* c[3][1] +=  b[3] * a[1];	       */
	      /* c[4][0] +=  b[4] * a[0];	       */
	      /* c[5][1] +=  b[5] * a[1];	       */
	      /* c[6][0] +=  b[6] * a[0];	       */
	      /* c[7][1] +=  b[7] * a[1];	       */

	    }
      
	    /* store C in register blocks. */
	    for (ri = 0; ri < REG_I; ri++) {
	      for (rj = 0; rj < REG_J; rj++) {
		Cj[i + ri + (rj)*LDA] = c[ri][rj];
	      }
	    }
	  }
	  
	  
	  
	  
	}
    /* We only care about performance for 32x32 matrices and 2 cores. Otherwise just naive mat_mul */
  } else {
    if (coreid > 0)
      return;
    
    for ( i = 0; i < lda; i++ )
      for ( j = 0; j < lda; j++ )  
	for ( k = 0; k < lda; k++ ) 
	  C[i + j*lda] += A[j*lda + k] * B[k*lda + i];
  }
}
