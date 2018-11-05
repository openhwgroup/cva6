#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
    int i, j, k;
    data_t B_trans[32*32];
    data_t acc_temp0, acc_temp1;
    data_t *A_j, *B_i;
    data_t *A_j_k, *B_i_k;
    int z;

    //for (i = 0; i < 32; i++) {
    //    for (j = 0; j < 32; j++) {
    //        B_trans[i*lda+j] = B[i+j*lda];
    //    }
    //}

    if (coreid == 0) {
        for (i = 0; i < 32; i++) {
            B_i = B_trans+i*32;
            for (z = 0; z < 32; z++) {
                *(B_i+z) = B[i+z*32];
            }
            for (j = 0; j < 16; j+=2) {
                A_j = A+j*lda;
                acc_temp0 = 0;
                for (k = 0; k < 32; k+=8) {
                    A_j_k = A_j+k;
                    B_i_k = B_i+k;
                    acc_temp0 += *(A_j_k)     * *(B_i_k);
                    acc_temp0 += *(A_j_k + 1) * *(B_i_k + 1);
                    acc_temp0 += *(A_j_k + 2) * *(B_i_k + 2);
                    acc_temp0 += *(A_j_k + 3) * *(B_i_k + 3);
                    acc_temp0 += *(A_j_k + 4) * *(B_i_k + 4);
                    acc_temp0 += *(A_j_k + 5) * *(B_i_k + 5);
                    acc_temp0 += *(A_j_k + 6) * *(B_i_k + 6);
                    acc_temp0 += *(A_j_k + 7) * *(B_i_k + 7);
                }
                A_j += 32;

                acc_temp1 = 0;
                for (k = 0; k < 32; k+=8) {
                    acc_temp1 += *(A_j+k) * *(B_i+k);
                    acc_temp1 += *(A_j+k + 1) * *(B_i+k + 1);
                    acc_temp1 += *(A_j+k + 2) * *(B_i+k + 2);
                    acc_temp1 += *(A_j+k + 3) * *(B_i+k + 3);
                    acc_temp1 += *(A_j+k + 4) * *(B_i+k + 4);
                    acc_temp1 += *(A_j+k + 5) * *(B_i+k + 5);
                    acc_temp1 += *(A_j+k + 6) * *(B_i+k + 6);
                    acc_temp1 += *(A_j+k + 7) * *(B_i+k + 7);
                }

                C[i + j*lda] = acc_temp0;
                C[i + (j+1)*lda] = acc_temp1;
            }
        }
    }
    if (coreid == 1 || ncores == 1) {
        for (i = 0; i < 32; i++) {
            B_i = B_trans+i*32;
            for (z = 0; z < 32; z++) {
                *(B_i+z) = B[i+z*32];
            }
            for (j = 16; j < 32; j+=2) {
                A_j = A+j*lda;
                acc_temp0 = 0;
                for (k = 0; k < 32; k+=8) {
                    acc_temp0 += *(A_j+k) * *(B_i+k);
                    acc_temp0 += *(A_j+k + 1) * *(B_i+k + 1);
                    acc_temp0 += *(A_j+k + 2) * *(B_i+k + 2);
                    acc_temp0 += *(A_j+k + 3) * *(B_i+k + 3);
                    acc_temp0 += *(A_j+k + 4) * *(B_i+k + 4);
                    acc_temp0 += *(A_j+k + 5) * *(B_i+k + 5);
                    acc_temp0 += *(A_j+k + 6) * *(B_i+k + 6);
                    acc_temp0 += *(A_j+k + 7) * *(B_i+k + 7);
                }
                A_j += 32;

                acc_temp1 = 0;
                for (k = 0; k < 32; k+=8) {
                    acc_temp1 += *(A_j+k) * *(B_i+k);
                    acc_temp1 += *(A_j+k + 1) * *(B_i+k + 1);
                    acc_temp1 += *(A_j+k + 2) * *(B_i+k + 2);
                    acc_temp1 += *(A_j+k + 3) * *(B_i+k + 3);
                    acc_temp1 += *(A_j+k + 4) * *(B_i+k + 4);
                    acc_temp1 += *(A_j+k + 5) * *(B_i+k + 5);
                    acc_temp1 += *(A_j+k + 6) * *(B_i+k + 6);
                    acc_temp1 += *(A_j+k + 7) * *(B_i+k + 7);
                }
                C[i + j*lda] = acc_temp0;
                C[i + (j+1)*lda] = acc_temp1;
            }
        }
    }
}
