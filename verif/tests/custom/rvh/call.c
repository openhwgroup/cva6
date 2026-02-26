#include <stdio.h>

#include "utils.h"

#include "sbi.h"
#include "csr.h"
#include "trampoline.h"
#include "vm.h"
#include "call.h"

void change_mode() {
    struct sbiret r = sbi_ecall(SBI_EXT_EXTRA, SBI_EXTRA_CHANGE_MODE, 0, 0, 0, 0, 0, 0);
    if (r.error) {
        printf("%s : ecall returned an error\n", __FUNCTION__);
        panic();
    }
}

void call_flush_tlb(void) {
    struct sbiret r = sbi_ecall(SBI_EXT_EXTRA, SBI_EXTRA_FLUSH_TLB, 0, 0, 0, 0, 0, 0);
    if (r.error) {
        printf("%s : ecall returned an error\n", __FUNCTION__);
        panic();
    }
}

void call_flush_htlb(void) {
    struct sbiret r = sbi_ecall(SBI_EXT_EXTRA, SBI_EXTRA_FLUSH_HTLB, 0, 0, 0, 0, 0, 0);
    if (r.error) {
        printf("%s : ecall returned an error\n", __FUNCTION__);
        panic();
    }
}

void call_set_stvec(vec_f v) {
    struct sbiret r = sbi_ecall(SBI_EXT_EXTRA, SBI_EXTRA_SET_STVEC, (uint64_t)v, 0, 0, 0, 0, 0);
    if (r.error) {
        printf("%s : ecall returned an error\n", __FUNCTION__);
        panic();
    }
}

void forward_ecall(struct trap_context *tc) {
    struct sbiret r = sbi_ecall(tc->a7, tc->a6, tc->a0, tc->a1, tc->a2, tc->a3, tc->a4, tc->a5);
    tc->a0 = r.error;
    tc->a1 = r.value;
}

uint64_t handle_vs_call(void) {
    struct trap_context *tc = GET_TRAP_CONTEXT();
    switch (tc->a7) {
        case SBI_EXT_DBCN: {
            switch (tc->a6) {
                case SBI_EXT_DBCN_CONSOLE_READ:
                case SBI_EXT_DBCN_CONSOLE_WRITE:
                case SBI_EXT_DBCN_CONSOLE_WRITE_BYTE: {
                    forward_ecall(tc);
                    break;
                }
                default: {
                    tc->a0 = EXTRA_UNKNOWN;
                    goto unknown;
                }
            }
            break;
        }
        case SBI_EXT_EXTRA: {
            switch (tc->a6) {
                case SBI_EXTRA_CHANGE_MODE: {
                    tc->a0 = EXTRA_SUCCESS;
                    csr_write(CSR_SSCRATCH, NEXT_INSTRUCTION(csr_read(CSR_SEPC), 1));
                    RESTORE_CONTEXT();
                    asm volatile("csrr t0, sscratch\n"
                                 "jr t0\n");
                    break;
                }
                case SBI_EXTRA_FLUSH_TLB: {
                    flush_tlb();
                    tc->a0 = EXTRA_SUCCESS;
                    break;
                }
                case SBI_EXTRA_FLUSH_HTLB: {
                    flush_htlb();
                    tc->a0 = EXTRA_SUCCESS;
                    break;
                }
                case SBI_EXTRA_SET_STVEC: {
                    asm volatile("csrw stvec, %0" ::"r"(tc->a0) : "memory");
                    tc->a0 = EXTRA_SUCCESS;
                    break;
                }
                default: {
                    tc->a0 = EXTRA_ERROR;
                    goto error;
                }
            }
            break;
        }
        default: {
            tc->a0 = EXTRA_UNKNOWN;
            goto unknown;
        }
    }
    return EXTRA_SUCCESS;
error:
    return EXTRA_ERROR;
unknown:
    return EXTRA_UNKNOWN;
}
