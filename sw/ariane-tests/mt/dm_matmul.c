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
	static data_t B1[32*32];
	if (coreid==ncores-1){	
		for (i=0; i<lda*lda/ncores;i++)
		{
			B1[i]=B[i];
		}
	}
	else{
		for (i=lda*lda/ncores;i<lda*lda;i++)
			B1[i]=B[i];	
	}
	data_t temp=0;
	data_t temp1=0;
	data_t temp2=0;
	data_t temp3=0;
	data_t tempB=0;

	data_t temp_1=0;
	data_t temp1_1=0;
	data_t temp2_1=0;
	data_t temp3_1=0;
	data_t tempB_1=0;

	data_t temp_2=0;
	data_t temp1_2=0;
	data_t temp2_2=0;
	data_t temp3_2=0;
	data_t tempB_2=0;

	data_t temp_3=0;
	data_t temp1_3=0;
	data_t temp2_3=0;
	data_t temp3_3=0;
	data_t tempB_3=0;
	barrier(ncores);
	if (coreid!=ncores-1){
		for (i=space*coreid;i<max/4*4;i+=4)
		{
			for(j=0;j<lda/4*4;j+=4)
			{
				temp=C[j+i*lda];
				temp1=C[j+(i+1)*lda];
				temp2=C[j+(i+2)*lda];
				temp3=C[j+(i+3)*lda];
				temp_1=C[j+1+i*lda];
				temp1_1=C[j+1+(i+1)*lda];
				temp2_1=C[j+1+(i+2)*lda];
				temp3_1=C[j+1+(i+3)*lda];
				temp_2=C[j+2+i*lda];
				temp1_2=C[j+2+(i+1)*lda];
				temp2_2=C[j+2+(i+2)*lda];
				temp3_2=C[j+2+(i+3)*lda];
				temp_3=C[j+3+i*lda];
				temp1_3=C[j+3+(i+1)*lda];
				temp2_3=C[j+3+(i+2)*lda];
				temp3_3=C[j+3+(i+3)*lda];
				for (k=0;k<lda;k++)
				{
					tempB=B[j+k*lda];
					temp+=A[k+i*lda]*tempB;	
					temp1+=A[k+(i+1)*lda]*tempB;
					temp2+=A[k+(i+2)*lda]*tempB;
					temp3+=A[k+(i+3)*lda]*tempB;
					
					tempB_1=B[j+1+k*lda];
					temp_1+=A[k+i*lda]*tempB_1;	
					temp1_1+=A[k+(i+1)*lda]*tempB_1;
					temp2_1+=A[k+(i+2)*lda]*tempB_1;
					temp3_1+=A[k+(i+3)*lda]*tempB_1;
				
					tempB_2=B[j+2+k*lda];
					temp_2+=A[k+i*lda]*tempB_2;	
					temp1_2+=A[k+(i+1)*lda]*tempB_2;
					temp2_2+=A[k+(i+2)*lda]*tempB_2;
					temp3_2+=A[k+(i+3)*lda]*tempB_2;
				
					tempB_3=B[j+3+k*lda];
					temp_3+=A[k+i*lda]*tempB_3;	
					temp1_3+=A[k+(i+1)*lda]*tempB_3;
					temp2_3+=A[k+(i+2)*lda]*tempB_3;
					temp3_3+=A[k+(i+3)*lda]*tempB_3;
				}
				C[j+i*lda]=temp;
				C[j+(i+1)*lda]=temp1;
				C[j+(i+2)*lda]=temp2;
				C[j+(i+3)*lda]=temp3;
				
				C[j+1+i*lda]=temp_1;
				C[j+1+(i+1)*lda]=temp1_1;
				C[j+1+(i+2)*lda]=temp2_1;
				C[j+1+(i+3)*lda]=temp3_1;
				
				C[j+2+i*lda]=temp_2;
				C[j+2+(i+1)*lda]=temp1_2;
				C[j+2+(i+2)*lda]=temp2_2;
				C[j+2+(i+3)*lda]=temp3_2;

				C[j+3+i*lda]=temp_3;
				C[j+3+(i+1)*lda]=temp1_3;
				C[j+3+(i+2)*lda]=temp2_3;
				C[j+3+(i+3)*lda]=temp3_3;
				
			}
		}
	}
	else{
		for (i=space*coreid;i<lda/4*4;i+=4)
		{
			for(j=0;j<lda/4*4;j+=4)
			{
				temp=C[j+i*lda];
				temp1=C[j+(i+1)*lda];
				temp2=C[j+(i+2)*lda];
				temp3=C[j+(i+3)*lda];
				temp_1=C[j+1+i*lda];
				temp1_1=C[j+1+(i+1)*lda];
				temp2_1=C[j+1+(i+2)*lda];
				temp3_1=C[j+1+(i+3)*lda];
				temp_2=C[j+2+i*lda];
				temp1_2=C[j+2+(i+1)*lda];
				temp2_2=C[j+2+(i+2)*lda];
				temp3_2=C[j+2+(i+3)*lda];
				temp_3=C[j+3+i*lda];
				temp1_3=C[j+3+(i+1)*lda];
				temp2_3=C[j+3+(i+2)*lda];
				temp3_3=C[j+3+(i+3)*lda];
				for (k=0;k<lda;k++)
				{
					tempB=B1[j+k*lda];
					temp+=A[k+i*lda]*tempB;	
					temp1+=A[k+(i+1)*lda]*tempB;
					temp2+=A[k+(i+2)*lda]*tempB;
					temp3+=A[k+(i+3)*lda]*tempB;
					
					tempB_1=B1[j+1+k*lda];
					temp_1+=A[k+i*lda]*tempB_1;	
					temp1_1+=A[k+(i+1)*lda]*tempB_1;
					temp2_1+=A[k+(i+2)*lda]*tempB_1;
					temp3_1+=A[k+(i+3)*lda]*tempB_1;
				
					tempB_2=B1[j+2+k*lda];
					temp_2+=A[k+i*lda]*tempB_2;	
					temp1_2+=A[k+(i+1)*lda]*tempB_2;
					temp2_2+=A[k+(i+2)*lda]*tempB_2;
					temp3_2+=A[k+(i+3)*lda]*tempB_2;
				
					tempB_3=B1[j+3+k*lda];
					temp_3+=A[k+i*lda]*tempB_3;	
					temp1_3+=A[k+(i+1)*lda]*tempB_3;
					temp2_3+=A[k+(i+2)*lda]*tempB_3;
					temp3_3+=A[k+(i+3)*lda]*tempB_3;
				}
				C[j+i*lda]=temp;
				C[j+(i+1)*lda]=temp1;
				C[j+(i+2)*lda]=temp2;
				C[j+(i+3)*lda]=temp3;
				
				C[j+1+i*lda]=temp_1;
				C[j+1+(i+1)*lda]=temp1_1;
				C[j+1+(i+2)*lda]=temp2_1;
				C[j+1+(i+3)*lda]=temp3_1;
				
				C[j+2+i*lda]=temp_2;
				C[j+2+(i+1)*lda]=temp1_2;
				C[j+2+(i+2)*lda]=temp2_2;
				C[j+2+(i+3)*lda]=temp3_2;

				C[j+3+i*lda]=temp_3;
				C[j+3+(i+1)*lda]=temp1_3;
				C[j+3+(i+2)*lda]=temp2_3;
				C[j+3+(i+3)*lda]=temp3_3;
				
			}
		}
	}


	
 
}
