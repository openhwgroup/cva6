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
   int i, j, k, ii, jj, kk; 
   if(coreid > 1) return; 
  if (coreid || ncores == 1) { 
// for ( ii = 0; ii < 32; ii+=IC )
         for ( kk = 0; kk < 32; kk+=16 ) 
   for ( j = 0; j < 16; j++ )  
// for ( j = 0; j < 16; j++ )  
   {
      for ( i =  0; i < 32; i+=8 )
//    for ( i = ii; i < ii + IC && i < 32; i+=8 )
      {
         data_t temp0 = C[i+j*32];
         data_t temp1 = C[i+j*32+1];
         data_t temp2 = C[i+j*32+2];
         data_t temp3 = C[i+j*32+3];
         data_t temp4 = C[i+j*32+4];
         data_t temp5 = C[i+j*32+5];
         data_t temp6 = C[i+j*32+6];
         data_t temp7 = C[i+j*32+7];
         for ( k = kk; k < kk+16 && k < 32; k++ ) 
//       for ( k = 0; k < 32; k++ ) 
         {
            data_t tempA = A[j*32+k];
            temp0 += tempA * B[k*32 + i];
            temp1 += tempA * B[k*32 + i+1];
            temp2 += tempA * B[k*32 + i+2];
            temp3 += tempA * B[k*32 + i+3];
            temp4 += tempA * B[k*32 + i+4];
            temp5 += tempA * B[k*32 + i+5];
            temp6 += tempA * B[k*32 + i+6];
            temp7 += tempA * B[k*32 + i+7];
         }
         C[i+j*32] = temp0;
         C[i+j*32+1] = temp1;
         C[i+j*32+2] = temp2;
         C[i+j*32+3] = temp3;
         C[i+j*32+4] = temp4;
         C[i+j*32+5] = temp5;
         C[i+j*32+6] = temp6;
         C[i+j*32+7] = temp7;
      }
   } 
  } 
  if(coreid == 0){
// for ( ii = 0; ii < 32; ii+=IC )
         for ( kk = 0; kk < 32; kk+=16 ) 
   for ( j = 16; j < 32; j++ )  
// for ( j = 16; j < 32; j++ )  
   {
      for ( i =   0; i < 32; i+=8 )
//    for ( i = ii; i < ii + IC && i < 32; i+=8 )
      {
         data_t temp0 = C[i+j*32];
         data_t temp1 = C[i+j*32+1];
         data_t temp2 = C[i+j*32+2];
         data_t temp3 = C[i+j*32+3];
         data_t temp4 = C[i+j*32+4];
         data_t temp5 = C[i+j*32+5];
         data_t temp6 = C[i+j*32+6];
         data_t temp7 = C[i+j*32+7];
         for ( k = kk; k < kk+16 && k < 32; k++ ) 
         {
            data_t tempA = A[j*32+k];
            temp0 += tempA * B[k*32 + i];
            temp1 += tempA * B[k*32 + i+1];
            temp2 += tempA * B[k*32 + i+2];
            temp3 += tempA * B[k*32 + i+3];
            temp4 += tempA * B[k*32 + i+4];
            temp5 += tempA * B[k*32 + i+5];
            temp6 += tempA * B[k*32 + i+6];
            temp7 += tempA * B[k*32 + i+7];
         }
         C[i+j*32] = temp0;
         C[i+j*32+1] = temp1;
         C[i+j*32+2] = temp2;
         C[i+j*32+3] = temp3;
         C[i+j*32+4] = temp4;
         C[i+j*32+5] = temp5;
         C[i+j*32+6] = temp6;
         C[i+j*32+7] = temp7;
      }

   }
  } 
}
