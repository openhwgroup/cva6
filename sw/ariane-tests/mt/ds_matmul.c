#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
int i,j,k,a,b,b1,a1,a2,a3,c,c1,c2,c3,b2,b3;
        for (j=coreid*4; j<lda; j+=4*ncores){
                a=j*lda;
                a1=(j+1)*lda;
                a2=(j+2)*lda;
                a3=(j+3)*lda;
                for (k=0;k<lda; k+=2)
                {
                        b = k*lda;
                        b1 = (k+1)*lda;
                        for (i=0;i<lda;i++){
                                c = B[b+i];
                                c1 = B[b1+i];
                                C[i+a]+=A[a+k]*c;
                                C[i+a1]+=A[a1+k]*c;
                                C[i+a2]+=A[a2+k]*c;
                                C[i+a3]+=A[a3+k]*c;
                                C[i+a]+=A[a+k+1]*c1;
                                C[i+a1]+=A[a1+k+1]*c1;
                                C[i+a2]+=A[a2+k+1]*c1;
                                C[i+a3]+=A[a3+k+1]*c1;
}
}
}
}
