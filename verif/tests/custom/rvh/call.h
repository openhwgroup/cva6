#ifndef HMODE_CALL_H
#define HMODE_CALL_H

#include "util.h"
#include "types.h"

#define SBI_EXT_EXTRA 0x08000000

enum sbi_ext_extra {
    SBI_EXTRA_CHANGE_MODE,
    SBI_EXTRA_FLUSH_TLB,
    SBI_EXTRA_FLUSH_HTLB,
    SBI_EXTRA_SET_STVEC,
};

enum sbi_ext_extra_error { EXTRA_SUCCESS = 0, EXTRA_ERROR, EXTRA_UNKNOWN };

void change_mode(void);
void call_flush_tlb(void);
void call_flush_htlb(void);
void call_set_stvec(vec_f);
uint64_t handle_vs_call(void);

#endif //HMODE_CALL_H
