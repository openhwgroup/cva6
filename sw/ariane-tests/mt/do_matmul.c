#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
    int i, j, k;
    data_t acc_temp;
    data_t *A_j, *B_i;
    int j_start = coreid*(32/ncores);
    int j_end = (coreid+1)*(32/ncores);
    for ( i = 0; i < 32; i++ ) {
        B_i = B + i;
        for ( j = j_start; j < j_end; j++ )  
        {
            acc_temp = 0;
            A_j = A + j*32;
            for ( k = 0; k < 32; k++ ) 
            {
                acc_temp += *(A_j + k) * *(B_i + k*32);
            }
            C[i + j*32] = acc_temp;
        }
    }
}
