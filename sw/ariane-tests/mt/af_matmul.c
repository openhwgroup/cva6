#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
    size_t i, j, k, l;
  int row,row2, column, column2, column3, column4, column5, column6, column7, column8;
  data_t element, element2, element3, element4, element5, element6, element7, element8;
	data_t B1, B2, B3, B4;
  data_t temp_mat[32]={0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
  data_t temp_mat2[32]={0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	int local_lda = lda;

  for (l=coreid*local_lda/ncores; l<local_lda*(1+coreid)/ncores; l+=2){
    row=l*32;
    row2=(l+1)*32;
		//element = A[row];
		//element5 = A[row2];
    for (i=0; i<local_lda; i+=4){
      element = A[row+i];
      element2 = A[row+i+1];
      element3 = A[row+i+2];
      element4 = A[row+i+3];

      element5 = A[row2+i];
      element6 = A[row2+i+1];
      element7 = A[row2+i+2];
      element8 = A[row2+i+3];

      column=i*local_lda;
      column2=(i+1)*local_lda;
      column3=(i+2)*local_lda;
      column4=(i+3)*local_lda;

			B1 = B[column];
			B2 = B[column2];
			B3 = B[column3];
			B4 = B[column4];
	
      for (j=0; j<lda; j+=4){		
				temp_mat[j]+=element*B1+element2*B2+element3*B3+element4*B4;
				temp_mat[j+1]+=element*B[column+j+1]+element2*B[column2+j+1]+element3*B[column3+j+1]+element4*B[column4+j+1];
				temp_mat[j+2]+=element*B[column+j+2]+element2*B[column2+j+2]+element3*B[column3+j+2]+element4*B[column4+j+2];
				temp_mat[j+3]+=element*B[column+j+3]+element2*B[column2+j+3]+element3*B[column3+j+3]+element4*B[column4+j+3];

				temp_mat2[j]+=element5*B1+element6*B2+element7*B3+element8*B4;
				temp_mat2[j+1]+=element5*B[column+j+1]+element6*B[column2+j+1]+element7*B[column3+j+1]+element8*B[column4+j+1];
				temp_mat2[j+2]+=element5*B[column+j+2]+element6*B[column2+j+2]+element7*B[column3+j+2]+element8*B[column4+j+2];
				temp_mat2[j+3]+=element5*B[column+j+3]+element6*B[column2+j+3]+element7*B[column3+j+3]+element8*B[column4+j+3];

				B1 = B[column+j+4];
				B2 = B[column2+j+4];
				B3 = B[column3+j+4];
				B4 = B[column4+j+4];
		
				}
			//element = A[row+i+4];
			//element5 = A[row2+i+4];
      }

			for(k=0; k<local_lda; k++){
				C[row+k]=temp_mat[k];
				temp_mat[k]=0;
				C[row2+k]=temp_mat2[k];
				temp_mat2[k]=0;

				}

	
  }
   // ***************************** //
   // **** ADD YOUR CODE HERE ***** //
   // ***************************** //
   //
   // feel free to make a separate function for MI and MSI versions.

}
