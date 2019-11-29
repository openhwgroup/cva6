#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
    /* inline assembly */
    asm volatile("ecall");
    /* write something to stdout */
    printf("hello world!\n");
    return EXIT_SUCCESS;
}
