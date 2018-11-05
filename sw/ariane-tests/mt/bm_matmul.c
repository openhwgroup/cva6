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
    int i, j, k;
    int space=lda/ncores;
    int max= space*coreid+space;
	data_t temp=0;

	data_t temp1=0;
	data_t temp2=0;
	data_t temp3=0;
	data_t temp4=0;
	
	data_t temp_1=0;

	data_t temp1_1=0;
	data_t temp2_1=0;
	data_t temp3_1=0;
	data_t temp4_1=0;
	
	data_t temp_2=0;

	data_t temp1_2=0;
	data_t temp2_2=0;
	data_t temp3_2=0;
	data_t temp4_2=0;
	
	data_t temp_3=0;

	data_t temp1_3=0;
	data_t temp2_3=0;
	data_t temp3_3=0;
	data_t temp4_3=0;

	if (coreid!=ncores-1){
	//main loop
		for (i=space*coreid;i<max/4*4;i+=4)
		{
			for(j=0;j<lda;j+=4)
			{
				temp1=C[j+i*lda];
				temp2=C[j+1+i*lda];
				temp3=C[j+2+i*lda];
				temp4=C[j+3+i*lda];
		
				temp1_1=C[j+(i+1)*lda];
				temp2_1=C[j+1+(i+1)*lda];
				temp3_1=C[j+2+(i+1)*lda];
				temp4_1=C[j+3+(i+1)*lda];
				
				temp1_2=C[j+(i+2)*lda];
				temp2_2=C[j+1+(i+2)*lda];
				temp3_2=C[j+2+(i+2)*lda];
				temp4_2=C[j+3+(i+2)*lda];
				
				temp1_3=C[j+(i+3)*lda];
				temp2_3=C[j+1+(i+3)*lda];
				temp3_3=C[j+2+(i+3)*lda];
				temp4_3=C[j+3+(i+3)*lda];
				for (k=0;k<lda;k++)
				{
					temp=A[k+i*lda];
					temp1+=temp*B[j+k*lda];
					temp2+=temp*B[j+1+k*lda];
					temp3+=temp*B[j+2+k*lda];
					temp4+=temp*B[j+3+k*lda];
					
					temp_1=A[k+(i+1)*lda];
					temp1_1+=temp_1*B[j+k*lda];
					temp2_1+=temp_1*B[j+1+k*lda];
					temp3_1+=temp_1*B[j+2+k*lda];
					temp4_1+=temp_1*B[j+3+k*lda];
					
					temp_2=A[k+(i+2)*lda];
					temp1_2+=temp_2*B[j+k*lda];
					temp2_2+=temp_2*B[j+1+k*lda];
					temp3_2+=temp_2*B[j+2+k*lda];
					temp4_2+=temp_2*B[j+3+k*lda];
					
					temp_3=A[k+(i+3)*lda];
					temp1_3+=temp_3*B[j+k*lda];
					temp2_3+=temp_3*B[j+1+k*lda];
					temp3_3+=temp_3*B[j+2+k*lda];
					temp4_3+=temp_3*B[j+3+k*lda];

				}
				C[j+i*lda]=temp1;
				C[j+1+i*lda]=temp2;
				C[j+2+i*lda]=temp3;
				C[j+3+i*lda]=temp4;
				
				C[j+(i+1)*lda]=temp1_1;
				C[j+1+(i+1)*lda]=temp2_1;
				C[j+2+(i+1)*lda]=temp3_1;
				C[j+3+(i+1)*lda]=temp4_1;
				
				C[j+(i+2)*lda]=temp1_2;
				C[j+1+(i+2)*lda]=temp2_2;
				C[j+2+(i+2)*lda]=temp3_2;
				C[j+3+(i+2)*lda]=temp4_2;
				
				C[j+(i+3)*lda]=temp1_3;
				C[j+1+(i+3)*lda]=temp2_3;
				C[j+2+(i+3)*lda]=temp3_3;
				C[j+3+(i+3)*lda]=temp4_3;

			}
			
		}
		
	
		
	}
	
	//second core
	else{
		for (i=space*coreid;i<lda/4*4;i+=4)
		{
			for(j=0;j<lda;j+=4)
			{
				temp1=C[j+i*lda];
				temp2=C[j+1+i*lda];
				temp3=C[j+2+i*lda];
				temp4=C[j+3+i*lda];
		
				temp1_1=C[j+(i+1)*lda];
				temp2_1=C[j+1+(i+1)*lda];
				temp3_1=C[j+2+(i+1)*lda];
				temp4_1=C[j+3+(i+1)*lda];
				
				temp1_2=C[j+(i+2)*lda];
				temp2_2=C[j+1+(i+2)*lda];
				temp3_2=C[j+2+(i+2)*lda];
				temp4_2=C[j+3+(i+2)*lda];
				
				temp1_3=C[j+(i+3)*lda];
				temp2_3=C[j+1+(i+3)*lda];
				temp3_3=C[j+2+(i+3)*lda];
				temp4_3=C[j+3+(i+3)*lda];
				for (k=0;k<lda;k++)
				{
					temp=A[k+i*lda];
					temp1+=temp*B[j+k*lda];
					temp2+=temp*B[j+1+k*lda];
					temp3+=temp*B[j+2+k*lda];
					temp4+=temp*B[j+3+k*lda];
					
					temp_1=A[k+(i+1)*lda];
					temp1_1+=temp_1*B[j+k*lda];
					temp2_1+=temp_1*B[j+1+k*lda];
					temp3_1+=temp_1*B[j+2+k*lda];
					temp4_1+=temp_1*B[j+3+k*lda];
					
					temp_2=A[k+(i+2)*lda];
					temp1_2+=temp_2*B[j+k*lda];
					temp2_2+=temp_2*B[j+1+k*lda];
					temp3_2+=temp_2*B[j+2+k*lda];
					temp4_2+=temp_2*B[j+3+k*lda];
					
					temp_3=A[k+(i+3)*lda];
					temp1_3+=temp_3*B[j+k*lda];
					temp2_3+=temp_3*B[j+1+k*lda];
					temp3_3+=temp_3*B[j+2+k*lda];
					temp4_3+=temp_3*B[j+3+k*lda];

				}
				C[j+i*lda]=temp1;
				C[j+1+i*lda]=temp2;
				C[j+2+i*lda]=temp3;
				C[j+3+i*lda]=temp4;
				
				C[j+(i+1)*lda]=temp1_1;
				C[j+1+(i+1)*lda]=temp2_1;
				C[j+2+(i+1)*lda]=temp3_1;
				C[j+3+(i+1)*lda]=temp4_1;
				
				C[j+(i+2)*lda]=temp1_2;
				C[j+1+(i+2)*lda]=temp2_2;
				C[j+2+(i+2)*lda]=temp3_2;
				C[j+3+(i+2)*lda]=temp4_2;
				
				C[j+(i+3)*lda]=temp1_3;
				C[j+1+(i+3)*lda]=temp2_3;
				C[j+2+(i+3)*lda]=temp3_3;
				C[j+3+(i+3)*lda]=temp4_3;

			}
			
		}
		
	
	}
	
 
}
