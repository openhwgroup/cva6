#include <stdio.h>
#include <stdlib.h>

// This is an illegal instruction that is not decodable (in the C extension space)
static void illegalCExtOP() {
    asm(".short 0x9e41 \n");
    return;
}

// This is a decodable instruction with an illegal field (rd == 0 in c.addi4spn)
void illegalCExtRdOP() {
    asm(".short 0x0000 \n");
    return;
}

// This is a decodable instruction with an illegal CSR
void illegalCSROP() {
    asm volatile("csrr x0, 0x20");
    return;
}

// This is a decodable instruction in the B extension
void illegalBExtOP() {
    asm volatile(".word 0x601e9f13");
}

int main () {
    printf("Generate an undecodable C extension instruction\n");
    illegalCExtOP();

    printf("Generate a decoded but illegal C extension instruction\n");
    illegalCExtRdOP();

    printf("Generate a decoded CSR operation with invalid CSR\n");
    illegalCSROP();

    printf("Generate a decoded B extension that is unsupported\n");
    illegalBExtOP();

    printf("Complete illegal instruction - unreachable\n");
    fflush(0);
}
