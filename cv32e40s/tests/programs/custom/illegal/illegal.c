#include <stdio.h>
#include <stdlib.h>

static void illegalOP() {
    asm(".word 0x00000000 \n");
    return;
}

extern int _boot_value;
int main () {
    printf("Generate an illegal instruction\n");
    fflush(0);

    illegalOP();

    printf("Complete illegal instruction - unreachable\n");
    fflush(0);
}
