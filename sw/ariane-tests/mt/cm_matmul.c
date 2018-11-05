#include "stdlib.h"

#include "util.h"

#include "dataset.h"
void __attribute__((noinline)) matmul(const int coreid, const int ncores, const int lda,  const data_t A[], const data_t B[], data_t C[] )
{
    int i,j,k,l;
    data_t element1, element2, element3, element4, element5, element6, element7, element8;
    int row, row2;
    int column1, column2, column3, column4, column5, column6, column7, column8;
    data_t temp[32]={0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
    data_t temp2[32]={0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
    if (coreid == 0){
      for (i=0; i<lda; i+=2){
	row = i*lda;
	row2 = (i+1)*lda;
	for (j=0; j<16; j+=4){
	  element1 = A[row+j];
	  element2 = A[row+j+1];
	  element3 = A[row+j+2];
	  element4 = A[row+j+3];
	  column1 = j*32;
	  column2 = (j+1)*32;
	  column3 = (j+2)*32;
	  column4 = (j+3)*32;
	  element5 = A[row2+j];
	  element6 = A[row2+j+1];
	  element7 = A[row2+j+2];
	  element8 = A[row2+j+3];

	  for (k=0; k<32; k+=4){
	    temp[k]+=element1*B[column1+k]+element2*B[column2+k]+element3*B[column3+k]+element4*B[column4+k];
	    temp[k+1]+=element1*B[column1+k+1]+element2*B[column2+k+1]+element3*B[column3+k+1]+element4*B[column4+k+1];
	    temp[k+2]+=element1*B[column1+k+2]+element2*B[column2+k+2]+element3*B[column3+k+2]+element4*B[column4+k+2];
	    temp[k+3]+=element1*B[column1+k+3]+element2*B[column2+k+3]+element3*B[column3+k+3]+element4*B[column4+k+3];
	    temp2[k]+=element5*B[column1+k]+element6*B[column2+k]+element7*B[column3+k]+element8*B[column4+k];
	    temp2[k+1]+=element5*B[column1+k+1]+element6*B[column2+k+1]+element7*B[column3+k+1]+element8*B[column4+k+1];
	    temp2[k+2]+=element5*B[column1+k+2]+element6*B[column2+k+2]+element7*B[column3+k+2]+element8*B[column4+k+2];
	    temp2[k+3]+=element5*B[column1+k+3]+element6*B[column2+k+3]+element7*B[column3+k+3]+element8*B[column4+k+3];
	  }
	  if (j==12){
	    for (l=0; l<32; l++){
	      C[row+l]+=temp[l];
	      C[row2+l]+=temp2[l];
	      temp[l]=0;
	      temp2[l]=0;
	    }
	  }
	}
      }
    }
    if (coreid==1 || ncores == 1){
      for (i=0; i<32; i+=2){
	row = (31-i)*lda;
	row2 = (31-i-1)*lda;
	for (j=16; j<32; j+=4){
	  element1 = A[row+j];
	  element2 = A[row+j+1];
	  element3 = A[row+j+2];
	  element4 = A[row+j+3];
	  element5 = A[row2+j];
	  element6 = A[row2+j+1];
	  element7 = A[row2+j+2];
	  element8 = A[row2+j+3];
	  column1 = j*32;
	  column2 = (j+1)*32;
	  column3 = (j+2)*32;
	  column4 = (j+3)*32;
	  for (k=0; k<32; k+=4){
	    temp[k]+=element1*B[column1+k]+element2*B[column2+k]+element3*B[column3+k]+element4*B[column4+k];
	    temp[k+1]+=element1*B[column1+k+1]+element2*B[column2+k+1]+element3*B[column3+k+1]+element4*B[column4+k+1];
	    temp[k+2]+=element1*B[column1+k+2]+element2*B[column2+k+2]+element3*B[column3+k+2]+element4*B[column4+k+2];
	    temp[k+3]+=element1*B[column1+k+3]+element2*B[column2+k+3]+element3*B[column3+k+3]+element4*B[column4+k+3];
	    temp2[k]+=element5*B[column1+k]+element6*B[column2+k]+element7*B[column3+k]+element8*B[column4+k];
	    temp2[k+1]+=element5*B[column1+k+1]+element6*B[column2+k+1]+element7*B[column3+k+1]+element8*B[column4+k+1];
	    temp2[k+2]+=element5*B[column1+k+2]+element6*B[column2+k+2]+element7*B[column3+k+2]+element8*B[column4+k+2];
	    temp2[k+3]+=element5*B[column1+k+3]+element6*B[column2+k+3]+element7*B[column3+k+3]+element8*B[column4+k+3];
	  }
	  if (j==28){
	    for (l=0; l<32; l++){
	      C[row+l]+=temp[l];
	      C[row2+l]+=temp2[l];
	      temp[l]=0;
	      temp2[l]=0;
	    }
	  }
	}
      }
      }  
}
