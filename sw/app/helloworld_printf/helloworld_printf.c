#include <stdio.h>
#include <stdlib.h>
  
int main(void)
{

  printf("hello World!\n"); 
  
  //wait end of uart frame
  volatile int c, d;  
  for (c = 1; c <= 32767; c++)
    for (d = 1; d <= 32767; d++)
      {}
          
  return(0);
}

