#!/bin/bash

lo=0
hi=4096

# c00 user
#lo=3488
#hi=4096

(
    declare -i csr=$lo;
    printf "void read_csr() {\n"
    printf "    unsigned int csr_value = ~0;\n"
    printf "\n"
    while [ $csr -lt $hi ]; do
        printf "    csr_value = ~0;\n"
#        printf "    printf(\"Read CSR[%03X]\\\n\");\n" $csr
        printf "    __asm__ volatile(\"csrr %%0, 0x%03X\" : \"=r\"(csr_value));\n" $csr
#        printf "    printf(\"After  CSR[%03X]=%%08X\\\n\\\n\", csr_value);\n" $csr
        printf "\n"
    
        csr=$((csr + 1))
    done 
    printf "}\n"
) > all_csr_por.h

touch all_csr_por.c
