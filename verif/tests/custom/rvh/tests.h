#ifndef HMODE_TESTS_H
#define HMODE_TESTS_H

#include "types.h"

struct test_env {
    stvec_f set_stvec;
    tlb_f flush_tlb;
    int count;
    const uint64_t *const mapping_entries;
};

void test_timer(void);
void test_u_mode(void);
void test_vs_mode_1(void);
void test_vs_mode_2(void);
void test_vs_mode_3(void);
void test_vs_mode_4(void);
void test_vs_mode_5(void);
void test_satp(void);
void test_vsatp_simple(void);
void test_hgatp_simple(void);
void test_vsatp_full(void);
void test_hgatp_full(void);

#endif //HMODE_TESTS_H
