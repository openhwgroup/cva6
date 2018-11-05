#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   if(coreid > 1) return; 
  static __thread int i, j, k;
  static __thread data_t tempA0, tempA1, tempA2, tempA3, tempA4, tempA5, tempA6, tempA7;
  static __thread data_t tempC0, tempC1, tempC2, tempC3, tempC4, tempC5, tempC6, tempC7, tempC8, tempC9, tempC10, tempC11, tempC12, tempC13, tempC14, tempC15;

  static __thread int start, end, jStride, jToRow, jToCol;
  static data_t A1[1024], B1[1024];;
  
  start = coreid << 9;
  end = ((ncores == 1) ? 2 :(coreid+1)) << 9;
  jStride = 8;

  if (coreid == 0) { 
    for (j=start; j < end; j+=jStride) {
      jToRow = (j>>5)<<5;
      jToCol = j%32;
      tempC0  = 0;
      tempC1  = 0;
      tempC2  = 0;
      tempC3  = 0;
      tempC4  = 0;
      tempC5  = 0;
      tempC6  = 0;
      tempC7  = 0;
      for ( i=0; i < lda; i+=2 ) {
        tempA0 = A[i   + jToRow];
        tempA1 = A[i+1 + jToRow];
        tempC0  += tempA0 * B[(jToCol   ) + (i<<5)];
        tempC1  += tempA0 * B[(jToCol+1 ) + (i<<5)];
        tempC2  += tempA0 * B[(jToCol+2 ) + (i<<5)];
        tempC3  += tempA0 * B[(jToCol+3 ) + (i<<5)];
        tempC4  += tempA0 * B[(jToCol+4 ) + (i<<5)];
        tempC5  += tempA0 * B[(jToCol+5 ) + (i<<5)];
        tempC6  += tempA0 * B[(jToCol+6 ) + (i<<5)];
        tempC7  += tempA0 * B[(jToCol+7 ) + (i<<5)];
        tempC0  += tempA1 * B[(jToCol   ) + ((i+1)<<5)];
        tempC1  += tempA1 * B[(jToCol+1 ) + ((i+1)<<5)];
        tempC2  += tempA1 * B[(jToCol+2 ) + ((i+1)<<5)];
        tempC3  += tempA1 * B[(jToCol+3 ) + ((i+1)<<5)];
        tempC4  += tempA1 * B[(jToCol+4 ) + ((i+1)<<5)];
        tempC5  += tempA1 * B[(jToCol+5 ) + ((i+1)<<5)];
        tempC6  += tempA1 * B[(jToCol+6 ) + ((i+1)<<5)];
        tempC7  += tempA1 * B[(jToCol+7 ) + ((i+1)<<5)];
      }
      C[j] =tempC0;
      C[j + 1 ]=tempC1;
      C[j + 2 ]=tempC2;
      C[j + 3 ]=tempC3;
      C[j + 4 ]=tempC4;
      C[j + 5 ]=tempC5;
      C[j + 6 ]=tempC6;
      C[j + 7 ]=tempC7;
    }
  }
  else { 
    for (i = 0; i < 1024; i++) {
      A1[i] = A[i];
      B1[i] = B[i];
    }
    for (j=start; j < end; j+=jStride) {
      jToRow = (j>>5)<<5;
      jToCol = j%32;
      tempC0  = 0;
      tempC1  = 0;
      tempC2  = 0;
      tempC3  = 0;
      tempC4  = 0;
      tempC5  = 0;
      tempC6  = 0;
      tempC7  = 0;
      for ( i=0; i < lda; i+=2 ) {
        tempA0 = A1[i   + jToRow];
        tempA1 = A1[i+1 + jToRow];
        tempC0  += tempA0 * B1[(jToCol   ) + (i<<5)];
        tempC1  += tempA0 * B1[(jToCol+1 ) + (i<<5)];
        tempC2  += tempA0 * B1[(jToCol+2 ) + (i<<5)];
        tempC3  += tempA0 * B1[(jToCol+3 ) + (i<<5)];
        tempC4  += tempA0 * B1[(jToCol+4 ) + (i<<5)];
        tempC5  += tempA0 * B1[(jToCol+5 ) + (i<<5)];
        tempC6  += tempA0 * B1[(jToCol+6 ) + (i<<5)];
        tempC7  += tempA0 * B1[(jToCol+7 ) + (i<<5)];
        tempC0  += tempA1 * B1[(jToCol   ) + ((i+1)<<5)];
        tempC1  += tempA1 * B1[(jToCol+1 ) + ((i+1)<<5)];
        tempC2  += tempA1 * B1[(jToCol+2 ) + ((i+1)<<5)];
        tempC3  += tempA1 * B1[(jToCol+3 ) + ((i+1)<<5)];
        tempC4  += tempA1 * B1[(jToCol+4 ) + ((i+1)<<5)];
        tempC5  += tempA1 * B1[(jToCol+5 ) + ((i+1)<<5)];
        tempC6  += tempA1 * B1[(jToCol+6 ) + ((i+1)<<5)];
        tempC7  += tempA1 * B1[(jToCol+7 ) + ((i+1)<<5)];
      }
      C[j] =tempC0;
      C[j + 1 ]=tempC1;
      C[j + 2 ]=tempC2;
      C[j + 3 ]=tempC3;
      C[j + 4 ]=tempC4;
      C[j + 5 ]=tempC5;
      C[j + 6 ]=tempC6;
      C[j + 7 ]=tempC7;
    }
  }
}
