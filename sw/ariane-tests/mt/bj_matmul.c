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
    
    int m, i, j, k, iB0, iB1;
    data_t tempC0, tempC1, tempC2, tempC3, tempC4, tempC5, tempC6, tempC7;
    data_t tempA0, tempA1;
    
   if(coreid > 1) return; 
    if (coreid == 0){
        for (m = 0; m < 2; m++){
            for (j = 0; j < lda/2; j++){
                for (i = 0; i < lda; i+=8){
                    tempC0 = C[i + j*lda];
                    tempC1 = C[i + j*lda+1];
                    tempC2 = C[i + j*lda+2];
                    tempC3 = C[i + j*lda+3];
                    tempC4 = C[i + j*lda+4];
                    tempC5 = C[i + j*lda+5];
                    tempC6 = C[i + j*lda+6];
                    tempC7 = C[i + j*lda+7];
                    iB0 = m*lda*lda/2+i;
                    iB1 = iB0+lda;
                    for (k = m*lda/2; k < (m+1)*lda/2; k+=2){
                        tempA0 = A[j*lda+k];
                        tempA1 = A[j*lda+k+1];
                        tempC0 += tempA0*B[iB0]+tempA1*B[iB1];
                        tempC1 += tempA0*B[iB0+1]+tempA1*B[iB1+1];
                        tempC2 += tempA0*B[iB0+2]+tempA1*B[iB1+2];
                        tempC3 += tempA0*B[iB0+3]+tempA1*B[iB1+3];
                        tempC4 += tempA0*B[iB0+4]+tempA1*B[iB1+4];
                        tempC5 += tempA0*B[iB0+5]+tempA1*B[iB1+5];
                        tempC6 += tempA0*B[iB0+6]+tempA1*B[iB1+6];
                        tempC7 += tempA0*B[iB0+7]+tempA1*B[iB1+7];
                        iB0 += 2*lda;
                        iB1 += 2*lda;
                        
                    }
                    C[i + j*lda] = tempC0;
                    C[i + j*lda + 1] = tempC1;
                    C[i + j*lda + 2] = tempC2;
                    C[i + j*lda + 3] = tempC3;
                    C[i + j*lda + 4] = tempC4;
                    C[i + j*lda + 5] = tempC5;
                    C[i + j*lda + 6] = tempC6;
                    C[i + j*lda + 7] = tempC7;
                }
            }
        }
    }
    if(coreid == 1  || ncores == 1) {
        for (m = 2; m > 0; m--){
            for (j = lda-1; j >= lda/2; j--){
                for (i = lda-1; i >= 0; i-=8){
                    tempC0 = C[i + j*lda];
                    tempC1 = C[i + j*lda - 1];
                    tempC2 = C[i + j*lda - 2];
                    tempC3 = C[i + j*lda - 3];
                    tempC4 = C[i + j*lda - 4];
                    tempC5 = C[i + j*lda - 5];
                    tempC6 = C[i + j*lda - 6];
                    tempC7 = C[i + j*lda - 7];
                    for (k = m*lda/2-1; k >= (m-1)*lda/2; k-=2){
                        tempA0 = A[j*lda+k];
                        tempA1 = A[j*lda+k-1];
                        tempC0 += tempA0*B[k*lda+i]+tempA1*B[(k-1)*lda+i];
                        tempC1 += tempA0*B[k*lda+i-1]+tempA1*B[(k-1)*lda+i-1];
                        tempC2 += tempA0*B[k*lda+i-2]+tempA1*B[(k-1)*lda+i-2];
                        tempC3 += tempA0*B[k*lda+i-3]+tempA1*B[(k-1)*lda+i-3];
                        tempC4 += tempA0*B[k*lda+i-4]+tempA1*B[(k-1)*lda+i-4];
                        tempC5 += tempA0*B[k*lda+i-5]+tempA1*B[(k-1)*lda+i-5];
                        tempC6 += tempA0*B[k*lda+i-6]+tempA1*B[(k-1)*lda+i-6];
                        tempC7 += tempA0*B[k*lda+i-7]+tempA1*B[(k-1)*lda+i-7];
                    }
                    C[i + j*lda] = tempC0;
                    C[i + j*lda - 1] = tempC1;
                    C[i + j*lda - 2] = tempC2;
                    C[i + j*lda - 3] = tempC3;
                    C[i + j*lda - 4] = tempC4;
                    C[i + j*lda - 5] = tempC5;
                    C[i + j*lda - 6] = tempC6;
                    C[i + j*lda - 7] = tempC7;
                }
            }
        }
    }
}
