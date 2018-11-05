#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   
    if(coreid > 1) return; 
    static __thread int i, j, k;
    static __thread data_t tempA0, tempA1, tempA2, tempA3, tempA4, tempA5, tempA6, tempA7;
    static __thread data_t tempC0, tempC1, tempC2, tempC3, tempC4, tempC5, tempC6, tempC7; //tempC8, tempC9, tempC10, tempC11, tempC12, tempC13, tempC14, tempC15;

    static __thread int start, end, jStride, jToRow, jToCol, iToRow;

    start = coreid << 9;
    end = ((ncores == 1) ? 2 : (coreid+1)) << 9;
    jStride = 8;

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
      //tempC8  = 0;
      //tempC9  = 0;
      //tempC10 = 0;
      //tempC11 = 0;
      //tempC12 = 0;
      //tempC13 = 0;
      //tempC14 = 0;
      //tempC15 = 0;
      
      for ( i=0; i < lda; i+=2 ) {
        iToRow = i << 5;

        tempA0 = A[i   + jToRow];
        tempA1 = A[i+1 + jToRow];
        //tempA2 = A[i+2 + jToRow];
        //tempA3 = A[i+3 + jToRow];
        //tempA4 = A[i+4 + jToRow];
        //tempA5 = A[i+5 + jToRow];
        //tempA6 = A[i+6 + jToRow];
        //tempA7 = A[i+7 + jToRow];
        
        tempC0  += tempA0 * B[(jToCol   ) + (iToRow)];
        tempC1  += tempA0 * B[(jToCol+1 ) + (iToRow)];
        tempC2  += tempA0 * B[(jToCol+2 ) + (iToRow)];
        tempC3  += tempA0 * B[(jToCol+3 ) + (iToRow)];
        tempC4  += tempA0 * B[(jToCol+4 ) + (iToRow)];
        tempC5  += tempA0 * B[(jToCol+5 ) + (iToRow)];
        tempC6  += tempA0 * B[(jToCol+6 ) + (iToRow)];
        tempC7  += tempA0 * B[(jToCol+7 ) + (iToRow)];
        //tempC8  += tempA0 * B[(jToCol+8 ) + (iToRow)];
        //tempC9  += tempA0 * B[(jToCol+9 ) + (iToRow)];
        //tempC10 += tempA0 * B[(jToCol+10) + (iToRow)];
        //tempC11 += tempA0 * B[(jToCol+11) + (iToRow)];
        //tempC12 += tempA0 * B[(jToCol+12) + (iToRow)];
        //tempC13 += tempA0 * B[(jToCol+13) + (iToRow)];
        //tempC14 += tempA0 * B[(jToCol+14) + (iToRow)];
        //tempC15 += tempA0 * B[(jToCol+15) + (iToRow)];
        
        iToRow += 32;
        tempC0  += tempA1 * B[(jToCol   ) + (iToRow)];
        tempC1  += tempA1 * B[(jToCol+1 ) + (iToRow)];
        tempC2  += tempA1 * B[(jToCol+2 ) + (iToRow)];
        tempC3  += tempA1 * B[(jToCol+3 ) + (iToRow)];
        tempC4  += tempA1 * B[(jToCol+4 ) + (iToRow)];
        tempC5  += tempA1 * B[(jToCol+5 ) + (iToRow)];
        tempC6  += tempA1 * B[(jToCol+6 ) + (iToRow)];
        tempC7  += tempA1 * B[(jToCol+7 ) + (iToRow)];
        //tempC8  += tempA1 * B[(jToCol+8 ) + (iToRow+32)];
        //tempC9  += tempA1 * B[(jToCol+9 ) + (iToRow+32)];
        //tempC10 += tempA1 * B[(jToCol+10) + (iToRow+32)];
        //tempC11 += tempA1 * B[(jToCol+11) + (iToRow+32)];
        //tempC12 += tempA1 * B[(jToCol+12) + (iToRow+32)];
        //tempC13 += tempA1 * B[(jToCol+13) + (iToRow+32)];
        //tempC14 += tempA1 * B[(jToCol+14) + (iToRow+32)];
        //tempC15 += tempA1 * B[(jToCol+15) + (iToRow+32)];
        
        //iToRow += 32;
        //tempC0  += tempA2 * B[(jToCol   ) + (iToRow)];
        //tempC1  += tempA2 * B[(jToCol+1 ) + (iToRow)];
        //tempC2  += tempA2 * B[(jToCol+2 ) + (iToRow)];
        //tempC3  += tempA2 * B[(jToCol+3 ) + (iToRow)];
        //tempC4  += tempA2 * B[(jToCol+4 ) + (iToRow)];
        //tempC5  += tempA2 * B[(jToCol+5 ) + (iToRow)];
        //tempC6  += tempA2 * B[(jToCol+6 ) + (iToRow)];
        //tempC7  += tempA2 * B[(jToCol+7 ) + (iToRow)];
        //tempC8  += tempA2 * B[(jToCol+8 ) + (iToRow)];
        //tempC9  += tempA2 * B[(jToCol+9 ) + (iToRow)];
        //tempC10 += tempA2 * B[(jToCol+10) + (iToRow)];
        //tempC11 += tempA2 * B[(jToCol+11) + (iToRow)];
        //tempC12 += tempA2 * B[(jToCol+12) + (iToRow)];
        //tempC13 += tempA2 * B[(jToCol+13) + (iToRow)];
        //tempC14 += tempA2 * B[(jToCol+14) + (iToRow)];
        //tempC15 += tempA2 * B[(jToCol+15) + (iToRow)];
        
        //iToRow += 32;
        //tempC0  += tempA3 * B[(jToCol   ) + (iToRow)];
        //tempC1  += tempA3 * B[(jToCol+1 ) + (iToRow)];
        //tempC2  += tempA3 * B[(jToCol+2 ) + (iToRow)];
        //tempC3  += tempA3 * B[(jToCol+3 ) + (iToRow)];
        //tempC4  += tempA3 * B[(jToCol+4 ) + (iToRow)];
        //tempC5  += tempA3 * B[(jToCol+5 ) + (iToRow)];
        //tempC6  += tempA3 * B[(jToCol+6 ) + (iToRow)];
        //tempC7  += tempA3 * B[(jToCol+7 ) + (iToRow)];
        //tempC8  += tempA3 * B[(jToCol+8 ) + (iToRow)];
        //tempC9  += tempA3 * B[(jToCol+9 ) + (iToRow)];
        //tempC10 += tempA3 * B[(jToCol+10) + (iToRow)];
        //tempC11 += tempA3 * B[(jToCol+11) + (iToRow)];
        //tempC12 += tempA3 * B[(jToCol+12) + (iToRow)];
        //tempC13 += tempA3 * B[(jToCol+13) + (iToRow)];
        //tempC14 += tempA3 * B[(jToCol+14) + (iToRow)];
        //tempC15 += tempA3 * B[(jToCol+15) + (iToRow)];
        
        //iToRow += 32;
        //tempC0 += tempA4 * B[(jToCol   ) + (iToRow)];
        //tempC1 += tempA4 * B[(jToCol+1 ) + (iToRow)];
        //tempC2 += tempA4 * B[(jToCol+2 ) + (iToRow)];
        //tempC3 += tempA4 * B[(jToCol+3 ) + (iToRow)];
        //tempC4 += tempA4 * B[(jToCol+4 ) + (iToRow)];
        //tempC5 += tempA4 * B[(jToCol+5 ) + (iToRow)];
        //tempC6 += tempA4 * B[(jToCol+6 ) + (iToRow)];
        //tempC7 += tempA4 * B[(jToCol+7 ) + (iToRow)];
        //
        //iToRow += 32;
        //tempC0 += tempA5 * B[(jToCol   ) + (iToRow)];
        //tempC1 += tempA5 * B[(jToCol+1 ) + (iToRow)];
        //tempC2 += tempA5 * B[(jToCol+2 ) + (iToRow)];
        //tempC3 += tempA5 * B[(jToCol+3 ) + (iToRow)];
        //tempC4 += tempA5 * B[(jToCol+4 ) + (iToRow)];
        //tempC5 += tempA5 * B[(jToCol+5 ) + (iToRow)];
        //tempC6 += tempA5 * B[(jToCol+6 ) + (iToRow)];
        //tempC7 += tempA5 * B[(jToCol+7 ) + (iToRow)];
        //
        //iToRow += 32;
        //tempC0 += tempA6 * B[(jToCol   ) + (iToRow)];
        //tempC1 += tempA6 * B[(jToCol+1 ) + (iToRow)];
        //tempC2 += tempA6 * B[(jToCol+2 ) + (iToRow)];
        //tempC3 += tempA6 * B[(jToCol+3 ) + (iToRow)];
        //tempC4 += tempA6 * B[(jToCol+4 ) + (iToRow)];
        //tempC5 += tempA6 * B[(jToCol+5 ) + (iToRow)];
        //tempC6 += tempA6 * B[(jToCol+6 ) + (iToRow)];
        //tempC7 += tempA6 * B[(jToCol+7 ) + (iToRow)];
        //
        //iToRow += 32;
        //tempC0 += tempA7 * B[(jToCol   ) + (iToRow)];
        //tempC1 += tempA7 * B[(jToCol+1 ) + (iToRow)];
        //tempC2 += tempA7 * B[(jToCol+2 ) + (iToRow)];
        //tempC3 += tempA7 * B[(jToCol+3 ) + (iToRow)];
        //tempC4 += tempA7 * B[(jToCol+4 ) + (iToRow)];
        //tempC5 += tempA7 * B[(jToCol+5 ) + (iToRow)];
        //tempC6 += tempA7 * B[(jToCol+6 ) + (iToRow)];
        //tempC7 += tempA7 * B[(jToCol+7 ) + (iToRow)];
        
      }
      C[j     ] = tempC0;
      C[j + 1 ] = tempC1;
      C[j + 2 ] = tempC2;
      C[j + 3 ] = tempC3;
      C[j + 4 ] = tempC4;
      C[j + 5 ] = tempC5;
      C[j + 6 ] = tempC6;
      C[j + 7 ] = tempC7;
      //C[j + 8 ] = tempC8 ;
      //C[j + 9 ] = tempC9 ;
      //C[j + 10] = tempC10;
      //C[j + 11] = tempC11;
      //C[j + 12] = tempC12;
      //C[j + 13] = tempC13;
      //C[j + 14] = tempC14;
      //C[j + 15] = tempC15;
    }
}
