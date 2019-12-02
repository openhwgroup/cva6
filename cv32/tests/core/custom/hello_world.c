#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
    /* inline assembly */
    asm volatile("ecall");
    /* write something to stdout */
    printf("\n\n\tHello World! This is the OpenHW Group CV32 RISC-V processor core!\n\n\n");
    return EXIT_SUCCESS;
}
