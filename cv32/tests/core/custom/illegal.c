#include <stdio.h>
#include <stdlib.h>

#include "startup/support.h"

extern int _boot_value;
int main () {
    printf("Generate an illegal instruction\n");
    fflush(0);

    illegalOP();

    printf("Complete illegal instruction - unreachable\n");
    fflush(0);
}
