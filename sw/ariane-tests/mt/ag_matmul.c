#include "stdlib.h"

#include "util.h"

#include "dataset.h"
#include "util.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{    
    int i, j, k;
    
    for ( i = 0; i < lda; i+=2 )
    {
        for (k = 0; k < lda; k+=4)
        {
            int d0 = B[k*lda + i];
            int c0 = B[k*lda + i + 1];
            int d1 = B[(k+1)*lda + i];
            int c1 = B[(k+1)*lda + i + 1];
            int d2 = B[(k+2)*lda + i];
            int c2 = B[(k+2)*lda + i + 1];
            int d3 = B[(k+3)*lda + i];
            int c3 = B[(k+3)*lda + i + 1];
            
            for ( j = coreid*(lda/ncores); j < (coreid+1)*(lda/ncores); j+=4)
            {
                
                int sum = A[j*lda + k] * d0;
                sum += A[j*lda + k + 1] * d1;
                sum += A[j*lda + k + 2] * d2;
                sum += A[j*lda + k + 3] * d3;
                C[j*lda +i] += sum;
                
                sum = A[j*lda + k] * c0;
                sum += A[j*lda + k + 1] * c1;
                sum += A[j*lda + k + 2] * c2;
                sum += A[j*lda + k + 3] * c3;
                C[j*lda + i + 1] += sum;
                
                sum = A[(j+1)*lda + k] * d0;
                sum += A[(j+1)*lda + k + 1] * d1;
                sum += A[(j+1)*lda + k + 2] * d2;
                sum += A[(j+1)*lda + k + 3] * d3;
                C[(j+1)*lda +i] += sum;
                
                sum = A[(j+1)*lda + k] * c0;
                sum += A[(j+1)*lda + k + 1] * c1;
                sum += A[(j+1)*lda + k + 2] * c2;
                sum += A[(j+1)*lda + k + 3] * c3;
                C[(j+1)*lda + i + 1] += sum;
                
                sum = A[(j+2)*lda + k] * d0;
                sum += A[(j+2)*lda + k + 1] * d1;
                sum += A[(j+2)*lda + k + 2] * d2;
                sum += A[(j+2)*lda + k + 3] * d3;
                C[(j+2)*lda +i] += sum;
                
                sum = A[(j+2)*lda + k] * c0;
                sum += A[(j+2)*lda + k + 1] * c1;
                sum += A[(j+2)*lda + k + 2] * c2;
                sum += A[(j+2)*lda + k + 3] * c3;
                C[(j+2)*lda + i + 1] += sum;
                
                sum = A[(j+3)*lda + k] * d0;
                sum += A[(j+3)*lda + k + 1] * d1;
                sum += A[(j+3)*lda + k + 2] * d2;
                sum += A[(j+3)*lda + k + 3] * d3;
                C[(j+3)*lda +i] += sum;
                
                sum = A[(j+3)*lda + k] * c0;
                sum += A[(j+3)*lda + k + 1] * c1;
                sum += A[(j+3)*lda + k + 2] * c2;
                sum += A[(j+3)*lda + k + 3] * c3;
                C[(j+3)*lda + i + 1] += sum;
                
            }
            barrier(ncores);
        }
    }
}
