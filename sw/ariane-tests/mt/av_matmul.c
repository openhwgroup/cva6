#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
   
	//-----------------------------------------------------------------version 2.16, optimize v2.15 get rid of tempb. MSI 83K.w/ test one 81K.

	
	static __thread data_t TempA[8];
	static __thread data_t TempB[8];
	static __thread data_t TempC[8];
	static __thread int j,m,n;
	
			if(coreid == 1 || ncores == 1 )
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
	     
		 

		 
		 
		 TempC[0] = TempA[0] * B[(0+8*m)*lda+0+8*n]; 
		 TempC[1] = TempA[0] * B[(0+8*m)*lda+1+8*n]; 
		 TempC[2] = TempA[0] * B[(0+8*m)*lda+2+8*n]; 
		 TempC[3] = TempA[0] * B[(0+8*m)*lda+3+8*n]; 
		 TempC[4] = TempA[0] * B[(0+8*m)*lda+4+8*n]; 
		 TempC[5] = TempA[0] * B[(0+8*m)*lda+5+8*n]; 
		 TempC[6] = TempA[0] * B[(0+8*m)*lda+6+8*n]; 
		 TempC[7] = TempA[0] * B[(0+8*m)*lda+7+8*n]; 
		 
		 
		 TempC[0] += TempA[1] * B[(1+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[1] * B[(1+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[1] * B[(1+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[1] * B[(1+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[1] * B[(1+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[1] * B[(1+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[1] * B[(1+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[1] * B[(1+8*m)*lda+7+8*n]; 
		 


		 TempC[0] += TempA[2] * B[(2+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[2] * B[(2+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[2] * B[(2+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[2] * B[(2+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[2] * B[(2+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[2] * B[(2+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[2] * B[(2+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[2] * B[(2+8*m)*lda+7+8*n]; 
		 


		 TempC[0] += TempA[3] * B[(3+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[3] * B[(3+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[3] * B[(3+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[3] * B[(3+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[3] * B[(3+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[3] * B[(3+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[3] * B[(3+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[3] * B[(3+8*m)*lda+7+8*n]; 

		 TempC[0] += TempA[4] * B[(4+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[4] * B[(4+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[4] * B[(4+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[4] * B[(4+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[4] * B[(4+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[4] * B[(4+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[4] * B[(4+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[4] * B[(4+8*m)*lda+7+8*n]; 


		 TempC[0] += TempA[5] * B[(5+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[5] * B[(5+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[5] * B[(5+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[5] * B[(5+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[5] * B[(5+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[5] * B[(5+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[5] * B[(5+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[5] * B[(5+8*m)*lda+7+8*n]; 
		 


		 TempC[0] += TempA[6] * B[(6+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[6] * B[(6+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[6] * B[(6+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[6] * B[(6+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[6] * B[(6+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[6] * B[(6+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[6] * B[(6+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[6] * B[(6+8*m)*lda+7+8*n]; 


		 TempC[0] += TempA[7] * B[(7+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[7] * B[(7+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[7] * B[(7+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[7] * B[(7+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[7] * B[(7+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[7] * B[(7+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[7] * B[(7+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[7] * B[(7+8*m)*lda+7+8*n]; 
		 

		
		 C[0+8*n+j*lda] += TempC[0];
		 C[1+8*n+j*lda] += TempC[1];
		 C[2+8*n+j*lda] += TempC[2];
		 C[3+8*n+j*lda] += TempC[3];
		 C[4+8*n+j*lda] += TempC[4];
		 C[5+8*n+j*lda] += TempC[5];
		 C[6+8*n+j*lda] += TempC[6];
		 C[7+8*n+j*lda] += TempC[7];
		 }
      }
	 }
	}
			if(coreid == 0)
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
	     
		 

		 
		 
		 TempC[0] = TempA[0] * B[(0+8*m)*lda+0+8*n]; 
		 TempC[1] = TempA[0] * B[(0+8*m)*lda+1+8*n]; 
		 TempC[2] = TempA[0] * B[(0+8*m)*lda+2+8*n]; 
		 TempC[3] = TempA[0] * B[(0+8*m)*lda+3+8*n]; 
		 TempC[4] = TempA[0] * B[(0+8*m)*lda+4+8*n]; 
		 TempC[5] = TempA[0] * B[(0+8*m)*lda+5+8*n]; 
		 TempC[6] = TempA[0] * B[(0+8*m)*lda+6+8*n]; 
		 TempC[7] = TempA[0] * B[(0+8*m)*lda+7+8*n]; 
		 
		 
		 TempC[0] += TempA[1] * B[(1+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[1] * B[(1+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[1] * B[(1+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[1] * B[(1+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[1] * B[(1+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[1] * B[(1+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[1] * B[(1+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[1] * B[(1+8*m)*lda+7+8*n]; 
		 


		 TempC[0] += TempA[2] * B[(2+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[2] * B[(2+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[2] * B[(2+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[2] * B[(2+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[2] * B[(2+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[2] * B[(2+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[2] * B[(2+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[2] * B[(2+8*m)*lda+7+8*n]; 
		 


		 TempC[0] += TempA[3] * B[(3+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[3] * B[(3+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[3] * B[(3+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[3] * B[(3+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[3] * B[(3+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[3] * B[(3+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[3] * B[(3+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[3] * B[(3+8*m)*lda+7+8*n]; 

		 TempC[0] += TempA[4] * B[(4+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[4] * B[(4+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[4] * B[(4+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[4] * B[(4+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[4] * B[(4+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[4] * B[(4+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[4] * B[(4+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[4] * B[(4+8*m)*lda+7+8*n]; 


		 TempC[0] += TempA[5] * B[(5+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[5] * B[(5+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[5] * B[(5+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[5] * B[(5+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[5] * B[(5+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[5] * B[(5+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[5] * B[(5+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[5] * B[(5+8*m)*lda+7+8*n]; 
		 


		 TempC[0] += TempA[6] * B[(6+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[6] * B[(6+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[6] * B[(6+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[6] * B[(6+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[6] * B[(6+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[6] * B[(6+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[6] * B[(6+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[6] * B[(6+8*m)*lda+7+8*n]; 


		 TempC[0] += TempA[7] * B[(7+8*m)*lda+0+8*n]; 
		 TempC[1] += TempA[7] * B[(7+8*m)*lda+1+8*n]; 
		 TempC[2] += TempA[7] * B[(7+8*m)*lda+2+8*n]; 
		 TempC[3] += TempA[7] * B[(7+8*m)*lda+3+8*n]; 
		 TempC[4] += TempA[7] * B[(7+8*m)*lda+4+8*n]; 
		 TempC[5] += TempA[7] * B[(7+8*m)*lda+5+8*n]; 
		 TempC[6] += TempA[7] * B[(7+8*m)*lda+6+8*n]; 
		 TempC[7] += TempA[7] * B[(7+8*m)*lda+7+8*n]; 
		 

		
		 C[0+8*n+j*lda] += TempC[0];
		 C[1+8*n+j*lda] += TempC[1];
		 C[2+8*n+j*lda] += TempC[2];
		 C[3+8*n+j*lda] += TempC[3];
		 C[4+8*n+j*lda] += TempC[4];
		 C[5+8*n+j*lda] += TempC[5];
		 C[6+8*n+j*lda] += TempC[6];
		 C[7+8*n+j*lda] += TempC[7];
		 }
      }
	 }
	}
}
