#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   int i,j,k,a,b,a1,a2,a3,c;
        for (j=coreid; j<lda; j+=4*ncores){
                a=j*lda;
                a1=(j+1*ncores)*lda;
                a2=(j+2*ncores)*lda;
                a3=(j+3*ncores)*lda;
               for (k=0;k<lda; k++)
                {
                        b = k*lda;
                        for (i=0;i<lda;i++){
                                c = B[b+i];
                                C[i+a]+=A[a+k]*c;
                                C[i+a1]+=A[a1+k]*c;
                                C[i+a2]+=A[a2+k]*c;
                                C[i+a3]+=A[a3+k]*c;
}
}
}
}
