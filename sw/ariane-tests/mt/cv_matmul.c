#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
	//----------------------------------------------------------------version 2.11 optmize j,use core 1 j from 0 to 15 MSI 98k i = j*lda
	//----------------------------------------------------------------version 2.12 not use i = j *lda MSI  95k
	static __thread data_t TempA[8];
	static __thread data_t TempB[8];
	static __thread int j,m,n,i,k;
	
	if(coreid == 1 || ncores == 1)
	{
	for ( j = 16; j < 32; j++ )
     {		
		  
      for ( m = 0; m < 4; m++ )  
      {
		  
		 TempA[0] = A[j*lda+0+8*m];
		 TempA[1] = A[j*lda+1+8*m];
		 TempA[2] = A[j*lda+2+8*m];
		 TempA[3] = A[j*lda+3+8*m];
		 TempA[4] = A[j*lda+4+8*m];
		 TempA[5] = A[j*lda+5+8*m];
		 TempA[6] = A[j*lda+6+8*m];
		 TempA[7] = A[j*lda+7+8*m];
		 
		for( n = 0; n < 4; n++)
		{
		 TempB[0] = B[(0+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(0+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(0+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(0+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(0+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(0+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(0+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(0+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[0] * TempB[0];
		 C[1+8*n+j*lda] += TempA[0] * TempB[1];
		 C[2+8*n+j*lda] += TempA[0] * TempB[2];
		 C[3+8*n+j*lda] += TempA[0] * TempB[3];
		 C[4+8*n+j*lda] += TempA[0] * TempB[4];
		 C[5+8*n+j*lda] += TempA[0] * TempB[5];
		 C[6+8*n+j*lda] += TempA[0] * TempB[6];
		 C[7+8*n+j*lda] += TempA[0] * TempB[7];
		 


		 TempB[0] = B[(1+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(1+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(1+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(1+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(1+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(1+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(1+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(1+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[1] * TempB[0];
		 C[1+8*n+j*lda] += TempA[1] * TempB[1];
		 C[2+8*n+j*lda] += TempA[1] * TempB[2];
		 C[3+8*n+j*lda] += TempA[1] * TempB[3];
		 C[4+8*n+j*lda] += TempA[1] * TempB[4];
		 C[5+8*n+j*lda] += TempA[1] * TempB[5];
		 C[6+8*n+j*lda] += TempA[1] * TempB[6];
		 C[7+8*n+j*lda] += TempA[1] * TempB[7];
		 


		 TempB[0] = B[(2+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(2+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(2+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(2+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(2+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(2+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(2+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(2+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[2] * TempB[0];
		 C[1+8*n+j*lda] += TempA[2] * TempB[1];
		 C[2+8*n+j*lda] += TempA[2] * TempB[2];
		 C[3+8*n+j*lda] += TempA[2] * TempB[3];
		 C[4+8*n+j*lda] += TempA[2] * TempB[4];
		 C[5+8*n+j*lda] += TempA[2] * TempB[5];
		 C[6+8*n+j*lda] += TempA[2] * TempB[6];
		 C[7+8*n+j*lda] += TempA[2] * TempB[7];
		 


		 TempB[0] = B[(3+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(3+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(3+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(3+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(3+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(3+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(3+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(3+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[3] * TempB[0];
		 C[1+8*n+j*lda] += TempA[3] * TempB[1];
		 C[2+8*n+j*lda] += TempA[3] * TempB[2];
		 C[3+8*n+j*lda] += TempA[3] * TempB[3];
		 C[4+8*n+j*lda] += TempA[3] * TempB[4];
		 C[5+8*n+j*lda] += TempA[3] * TempB[5];
		 C[6+8*n+j*lda] += TempA[3] * TempB[6];
		 C[7+8*n+j*lda] += TempA[3] * TempB[7];


		 TempB[0] = B[(4+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(4+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(4+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(4+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(4+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(4+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(4+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(4+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[4] * TempB[0];
		 C[1+8*n+j*lda] += TempA[4] * TempB[1];
		 C[2+8*n+j*lda] += TempA[4] * TempB[2];
		 C[3+8*n+j*lda] += TempA[4] * TempB[3];
		 C[4+8*n+j*lda] += TempA[4] * TempB[4];
		 C[5+8*n+j*lda] += TempA[4] * TempB[5];
		 C[6+8*n+j*lda] += TempA[4] * TempB[6];
		 C[7+8*n+j*lda] += TempA[4] * TempB[7];
		 


		 TempB[0] = B[(5+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(5+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(5+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(5+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(5+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(5+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(5+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(5+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[5] * TempB[0];
		 C[1+8*n+j*lda] += TempA[5] * TempB[1];
		 C[2+8*n+j*lda] += TempA[5] * TempB[2];
		 C[3+8*n+j*lda] += TempA[5] * TempB[3];
		 C[4+8*n+j*lda] += TempA[5] * TempB[4];
		 C[5+8*n+j*lda] += TempA[5] * TempB[5];
		 C[6+8*n+j*lda] += TempA[5] * TempB[6];
		 C[7+8*n+j*lda] += TempA[5] * TempB[7];
		 


		 TempB[0] = B[(6+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(6+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(6+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(6+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(6+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(6+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(6+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(6+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[6] * TempB[0];
		 C[1+8*n+j*lda] += TempA[6] * TempB[1];
		 C[2+8*n+j*lda] += TempA[6] * TempB[2];
		 C[3+8*n+j*lda] += TempA[6] * TempB[3];
		 C[4+8*n+j*lda] += TempA[6] * TempB[4];
		 C[5+8*n+j*lda] += TempA[6] * TempB[5];
		 C[6+8*n+j*lda] += TempA[6] * TempB[6];
		 C[7+8*n+j*lda] += TempA[6] * TempB[7];


		 TempB[0] = B[(7+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(7+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(7+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(7+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(7+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(7+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(7+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(7+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[7] * TempB[0];
		 C[1+8*n+j*lda] += TempA[7] * TempB[1];
		 C[2+8*n+j*lda] += TempA[7] * TempB[2];
		 C[3+8*n+j*lda] += TempA[7] * TempB[3];
		 C[4+8*n+j*lda] += TempA[7] * TempB[4];
		 C[5+8*n+j*lda] += TempA[7] * TempB[5];
		 C[6+8*n+j*lda] += TempA[7] * TempB[6];
		 C[7+8*n+j*lda] += TempA[7] * TempB[7];
		}

      }
	 }
	}
	if(coreid ==0)
		{
	for ( j = 0; j < 16; j++ )
     {		
		  
      for ( m = 0; m < 4; m++ )  
      {
		  
		 TempA[0] = A[j*lda+0+8*m];
		 TempA[1] = A[j*lda+1+8*m];
		 TempA[2] = A[j*lda+2+8*m];
		 TempA[3] = A[j*lda+3+8*m];
		 TempA[4] = A[j*lda+4+8*m];
		 TempA[5] = A[j*lda+5+8*m];
		 TempA[6] = A[j*lda+6+8*m];
		 TempA[7] = A[j*lda+7+8*m];
		 
		for( n = 0; n < 4; n++)
		{
		 TempB[0] = B[(0+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(0+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(0+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(0+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(0+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(0+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(0+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(0+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[0] * TempB[0];
		 C[1+8*n+j*lda] += TempA[0] * TempB[1];
		 C[2+8*n+j*lda] += TempA[0] * TempB[2];
		 C[3+8*n+j*lda] += TempA[0] * TempB[3];
		 C[4+8*n+j*lda] += TempA[0] * TempB[4];
		 C[5+8*n+j*lda] += TempA[0] * TempB[5];
		 C[6+8*n+j*lda] += TempA[0] * TempB[6];
		 C[7+8*n+j*lda] += TempA[0] * TempB[7];
		 


		 TempB[0] = B[(1+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(1+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(1+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(1+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(1+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(1+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(1+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(1+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[1] * TempB[0];
		 C[1+8*n+j*lda] += TempA[1] * TempB[1];
		 C[2+8*n+j*lda] += TempA[1] * TempB[2];
		 C[3+8*n+j*lda] += TempA[1] * TempB[3];
		 C[4+8*n+j*lda] += TempA[1] * TempB[4];
		 C[5+8*n+j*lda] += TempA[1] * TempB[5];
		 C[6+8*n+j*lda] += TempA[1] * TempB[6];
		 C[7+8*n+j*lda] += TempA[1] * TempB[7];
		 


		 TempB[0] = B[(2+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(2+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(2+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(2+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(2+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(2+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(2+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(2+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[2] * TempB[0];
		 C[1+8*n+j*lda] += TempA[2] * TempB[1];
		 C[2+8*n+j*lda] += TempA[2] * TempB[2];
		 C[3+8*n+j*lda] += TempA[2] * TempB[3];
		 C[4+8*n+j*lda] += TempA[2] * TempB[4];
		 C[5+8*n+j*lda] += TempA[2] * TempB[5];
		 C[6+8*n+j*lda] += TempA[2] * TempB[6];
		 C[7+8*n+j*lda] += TempA[2] * TempB[7];
		 


		 TempB[0] = B[(3+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(3+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(3+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(3+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(3+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(3+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(3+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(3+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[3] * TempB[0];
		 C[1+8*n+j*lda] += TempA[3] * TempB[1];
		 C[2+8*n+j*lda] += TempA[3] * TempB[2];
		 C[3+8*n+j*lda] += TempA[3] * TempB[3];
		 C[4+8*n+j*lda] += TempA[3] * TempB[4];
		 C[5+8*n+j*lda] += TempA[3] * TempB[5];
		 C[6+8*n+j*lda] += TempA[3] * TempB[6];
		 C[7+8*n+j*lda] += TempA[3] * TempB[7];


		 TempB[0] = B[(4+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(4+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(4+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(4+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(4+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(4+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(4+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(4+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[4] * TempB[0];
		 C[1+8*n+j*lda] += TempA[4] * TempB[1];
		 C[2+8*n+j*lda] += TempA[4] * TempB[2];
		 C[3+8*n+j*lda] += TempA[4] * TempB[3];
		 C[4+8*n+j*lda] += TempA[4] * TempB[4];
		 C[5+8*n+j*lda] += TempA[4] * TempB[5];
		 C[6+8*n+j*lda] += TempA[4] * TempB[6];
		 C[7+8*n+j*lda] += TempA[4] * TempB[7];
		 


		 TempB[0] = B[(5+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(5+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(5+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(5+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(5+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(5+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(5+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(5+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[5] * TempB[0];
		 C[1+8*n+j*lda] += TempA[5] * TempB[1];
		 C[2+8*n+j*lda] += TempA[5] * TempB[2];
		 C[3+8*n+j*lda] += TempA[5] * TempB[3];
		 C[4+8*n+j*lda] += TempA[5] * TempB[4];
		 C[5+8*n+j*lda] += TempA[5] * TempB[5];
		 C[6+8*n+j*lda] += TempA[5] * TempB[6];
		 C[7+8*n+j*lda] += TempA[5] * TempB[7];
		 


		 TempB[0] = B[(6+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(6+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(6+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(6+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(6+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(6+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(6+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(6+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[6] * TempB[0];
		 C[1+8*n+j*lda] += TempA[6] * TempB[1];
		 C[2+8*n+j*lda] += TempA[6] * TempB[2];
		 C[3+8*n+j*lda] += TempA[6] * TempB[3];
		 C[4+8*n+j*lda] += TempA[6] * TempB[4];
		 C[5+8*n+j*lda] += TempA[6] * TempB[5];
		 C[6+8*n+j*lda] += TempA[6] * TempB[6];
		 C[7+8*n+j*lda] += TempA[6] * TempB[7];


		 TempB[0] = B[(7+8*m)*lda+0+8*n]; 
		 TempB[1] = B[(7+8*m)*lda+1+8*n]; 
		 TempB[2] = B[(7+8*m)*lda+2+8*n]; 
		 TempB[3] = B[(7+8*m)*lda+3+8*n]; 
		 TempB[4] = B[(7+8*m)*lda+4+8*n]; 
		 TempB[5] = B[(7+8*m)*lda+5+8*n]; 
		 TempB[6] = B[(7+8*m)*lda+6+8*n]; 
		 TempB[7] = B[(7+8*m)*lda+7+8*n]; 
		 
		 C[0+8*n+j*lda] += TempA[7] * TempB[0];
		 C[1+8*n+j*lda] += TempA[7] * TempB[1];
		 C[2+8*n+j*lda] += TempA[7] * TempB[2];
		 C[3+8*n+j*lda] += TempA[7] * TempB[3];
		 C[4+8*n+j*lda] += TempA[7] * TempB[4];
		 C[5+8*n+j*lda] += TempA[7] * TempB[5];
		 C[6+8*n+j*lda] += TempA[7] * TempB[6];
		 C[7+8*n+j*lda] += TempA[7] * TempB[7];
		}

      }
	 }
	}

	
}
