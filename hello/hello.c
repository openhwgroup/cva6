//#include "util.h"
#include <stdio.h>

int main(int argc, char const *argv[]) {
    int a;
    int * b;
    b=(int *)0xC0000000;
    (*b)=2;
    a=b;
    printf("@ %x : %x \n", a, (*b) );
    return 0;
}

