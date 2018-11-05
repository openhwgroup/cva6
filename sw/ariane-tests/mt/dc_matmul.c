#include "stdlib.h"

#include "util.h"

#include "dataset.h"

#define REG_I 8
#define REG_J 2
#define BLOCK_I 32
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
    for (jj = start; jj < end; jj += BLOCK_J) {
      int kk_start= (coreid == 0 ? 0 : LDA/2) ,kk_end = (coreid == 0 ? LDA/2 : LDA);
      for (kk = kk_start; kk < kk_end; kk += BLOCK_K) {
	//  for (ii = 0; ii < LDA; ii += BLOCK_I)
	for (j = jj; j < MIN(end, jj + BLOCK_J); j += REG_J) {
	  Aj = A + j*LDA;
	  Cj = C + j*LDA;
	  for (i = 0; i < LDA/*, ii + BLOCK_I)*/; i += REG_I) {
	    /* Load C in register blocks. */
	    Bi = B + i;
	    for (ri = 0; ri < REG_I; ri++) {
	      for (rj = 0; rj < REG_J; rj++) {
		c[ri][rj] = Cj[i + ri + ( rj)*LDA];
	      }
	    }
	    
	    
	    for (k = kk; k < MIN(LDA, kk + BLOCK_K); k++) {
	      for (ri = 0; ri < REG_I; ri++) {
		b[ri] = Bi[k*LDA  + ri];
	      }
	      /* Compute C in register blocks. */
	      for (rj = 0; rj < REG_J; rj++) {
		a[rj] = Aj[(rj)*LDA + k];
		for (ri = 0; ri < REG_I; ri++) {
		  c[ri][rj] += a[rj] * b[ri];
		}
	      }
	    }
	    
	    /* store C in register blocks. */
	    for (ri = 0; ri < REG_I; ri++) {
	      for (rj = 0; rj < REG_J; rj++) {
		Cj[i + ri + ( rj)*LDA] = c[ri][rj];
	      }
	    }
	  }
	}
	/* barrier(nc); */

	/* kk_start= (coreid == 1 ? 0 : LDA/2); */
	/* kk_end = (coreid == 1 ? LDA/2 : LDA); */
	/* for (kk = kk_start; kk < kk_end; kk += BLOCK_K) { */
	/* //  for (ii = 0; ii < LDA; ii += BLOCK_I) */
	/* for (j = jj; j < MIN(end, jj + BLOCK_J); j += REG_J) { */
	/*   Aj = A + j*LDA; */
	/*   Cj = C + j*LDA; */
	/*   for (i = 0; i < LDA/\*, ii + BLOCK_I)*\/; i += REG_I) { */
	/*     /\* Load C in register blocks. *\/ */
	/*     Bi = B + i; */
	/*     for (ri = 0; ri < REG_I; ri++) { */
	/*       for (rj = 0; rj < REG_J; rj++) { */
	/* 	c[ri][rj] = Cj[i + ri + ( rj)*LDA]; */
	/*       } */
	/*     } */
	    
	    
	/*     for (k = kk; k < MIN(LDA, kk + BLOCK_K); k++) { */
	/*       for (ri = 0; ri < REG_I; ri++) { */
	/* 	b[ri] = Bi[k*LDA  + ri]; */
	/*       } */
	/*       /\* Compute C in register blocks. *\/ */
	/*       for (rj = 0; rj < REG_J; rj++) { */
	/* 	a[rj] = Aj[(rj)*LDA + k]; */
	/* 	for (ri = 0; ri < REG_I; ri++) { */
	/* 	  c[ri][rj] += a[rj] * b[ri]; */
	/* 	} */
	/*       } */
	/*     } */
	      
	    /* store C in register blocks. */
	/*     for (ri = 0; ri < REG_I; ri++) { */
    /* 	      for (rj = 0; rj < REG_J; rj++) { */
    /* 		Cj[i + ri + ( rj)*LDA] = c[ri][rj]; */
    /* 	      } */
    /* 	    } */
    /*   } */
    /* } */
      }
    }
  
    
    //barrier(nc);
    for (jj = start; jj < end; jj += BLOCK_J) {
      int kk_start= (coreid != 0 ? 0 : LDA/2), kk_end = (coreid != 0 ? LDA/2 : LDA);
      for (kk = kk_start; kk < kk_end; kk += BLOCK_K) {
    	//  for (ii = 0; ii < LDA; ii += BLOCK_I)
    	for (j = jj; j < MIN(end, jj + BLOCK_J); j += REG_J) {
    	  Aj = A + j*LDA;
    	  Cj = C + j*LDA;
    	  for (i = 0; i < LDA/*, ii + BLOCK_I)*/; i += REG_I) {
    	    /* Load C in register blocks. */
    	    Bi = B + i;
    	    for (ri = 0; ri < REG_I; ri++) {
    	      for (rj = 0; rj < REG_J; rj++) {
    		c[ri][rj] = Cj[i + ri + ( rj)*LDA];
    	      }
    	    }
	    
	    
    	    for (k = kk; k < MIN(LDA, kk + BLOCK_K); k++) {
    	      for (ri = 0; ri < REG_I; ri++) {
    		b[ri] = Bi[k*LDA  + ri];
    	      }
    	      /* Compute C in register blocks. */
    	      for (rj = 0; rj < REG_J; rj++) {
    		a[rj] = Aj[(rj)*LDA + k];
    		for (ri = 0; ri < REG_I; ri++) {
    		  c[ri][rj] += a[rj] * b[ri];
    		}
    	      }
    	    }
	    
    	      /* store C in register blocks. */
    	    for (ri = 0; ri < REG_I; ri++) {
    	      for (rj = 0; rj < REG_J; rj++) {
    		Cj[i + ri + ( rj)*LDA] = c[ri][rj];
    	      }
    	    }
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
