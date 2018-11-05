#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
  size_t i, j, k, l;
  int row,row2, column, column2, column3, column4, column5, column6, column7, column8;
  size_t max_dim = 32*32;
  data_t element, element2, element3, element4, element5, element6, element7, element8;
  data_t temp_mat[32]={0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
  data_t temp_mat2[32]={0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
  //for (i=coreid*max_dim/ncores; i<(max_dim/ncores+coreid*max_dim/ncores); i+=8){
  for (l=coreid*32/ncores; l<32*(1+coreid)/ncores; l+=2){
    row=l*32;
    row2=(l+1)*32;
    for (i=0; i<lda; i+=4){
      element = A[row+i];
      element2 = A[row+i+1];
      element3 = A[row+i+2];
      element4 = A[row+i+3];
      element5 = A[row2+i];
      element6 = A[row2+i+1];
      element7 = A[row2+i+2];
      element8 = A[row2+i+3];
      column=i*32;
      column2=(i+1)*32;
      column3=(i+2)*32;
      column4=(i+3)*32;
      for (j=0; j<32; j+=4){
	temp_mat[j]+=element*B[column+j]+element2*B[column2+j]+element3*B[column3+j]+element4*B[column4+j];
	temp_mat[j+1]+=element*B[column+j+1]+element2*B[column2+j+1]+element3*B[column3+j+1]+element4*B[column4+j+1];
	temp_mat[j+2]+=element*B[column+j+2]+element2*B[column2+j+2]+element3*B[column3+j+2]+element4*B[column4+j+2];
	temp_mat[j+3]+=element*B[column+j+3]+element2*B[column2+j+3]+element3*B[column3+j+3]+element4*B[column4+j+3];
	temp_mat2[j]+=element5*B[column+j]+element6*B[column2+j]+element7*B[column3+j]+element8*B[column4+j];
	temp_mat2[j+1]+=element5*B[column+j+1]+element6*B[column2+j+1]+element7*B[column3+j+1]+element8*B[column4+j+1];
	temp_mat2[j+2]+=element5*B[column+j+2]+element6*B[column2+j+2]+element7*B[column3+j+2]+element8*B[column4+j+2];
	temp_mat2[j+3]+=element5*B[column+j+3]+element6*B[column2+j+3]+element7*B[column3+j+3]+element8*B[column4+j+3];
      }
      /*if (i==28){
	for(k=0; k<32; k++){
	  C[row+k]=temp_mat[k];
	  C[row2+k]=temp_mat2[k];
	  temp_mat[k]=0;
	  temp_mat2[k]=0;
	}
	}*/
    }
    for(k=0; k<32; k++){
	  C[row+k]=temp_mat[k];
	  C[row2+k]=temp_mat2[k];
	  temp_mat[k]=0;
	  temp_mat2[k]=0;
    }
  }
  
   // ***************************** //
   // **** ADD YOUR CODE HERE ***** //
   // ***************************** //
   //
   // feel free to make a separate function for MI and MSI versions.

}
