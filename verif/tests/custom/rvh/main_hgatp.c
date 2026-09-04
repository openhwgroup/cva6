#include <stdio.h>

#include "main.h"
#include "tests.h"
#include "utils.h"
#include "mmode.h"
#include "vm.h"

int main(int argc, char* arg[]) {
    firmware_init();
    test_routine();
}

void test_routine(void) {
    build_page_tables();
    printf("\n============\n");
    reset();
    test_hgatp_simple();
    reset();
    test_hgatp_full();
    reset();
    printf("============\n");
}
