#include <stdio.h>

#include "utils.h"

#include "csr.h"
#include "vm.h"

__attribute__((naked, noreturn, aligned(4))) void panic(void) {
    exit(1);
}

void reset(void) {
    csr_write(CSR_STVEC, &panic_vector);
    csr_write(CSR_SEPC, &panic);
    csr_write(CSR_SIE, 0ul);
    csr_clear(CSR_SSTATUS, SR_SIE);
    csr_write(CSR_HSTATUS, 0ul);
    csr_write(CSR_HIE, 0ul);
    csr_write(CSR_HIDELEG, 0ul);
    csr_write(CSR_HEDELEG, 0ul);
    csr_write(CSR_HCOUNTEREN, 0ul);
    // Activate CBO
    csr_write(CSR_SENVCFG, ENVCFG_CBIE | ENVCFG_CBCFE | ENVCFG_CBZE);
    csr_write(CSR_HENVCFG, ENVCFG_CBIE | ENVCFG_CBCFE | ENVCFG_CBZE);
    csr_write(CSR_HGATP, 0ul);
    flush_htlb();
    csr_write(CSR_SATP, 0ul);
    flush_tlb();
}

__attribute__((noreturn, naked, aligned(4))) void panic_vector(void) {
    printf("Panic: ");
    if (csr_read(CSR_SCAUSE) & CAUSE_IRQ_FLAG) {
        switch (csr_read(CSR_SCAUSE)  & ~CAUSE_IRQ_FLAG) {
            case 1: {
                printf("Software Interrupt (HS-mode)");
                break;
            }
            case 2: {
                printf("Software Interrupt (VS-mode)");
                break;
            }
            case 3: {
                printf("Software Interrupt (M-mode)");
                break;
            }
            case 5: {
                printf("Timer Interrupt (HS-mode)");
                break;
            }
            case 6: {
                printf("Timer Interrupt (VS-mode)");
                break;
            }
            case 7: {
                printf("Timer Interrupt (M-mode)");
                break;
            }
            case 9: {
                printf("External Interrupt (HS-mode)");
                break;
            }
            case 10: {
                printf("External Interrupt (VS-mode)");
                break;
            }
            case 11: {
                printf("External Interrupt (M-mode)");
                break;
            }
            default: {
                printf("Unsupported Interrupt");
            }
        }
    } else {
        switch (csr_read(CSR_SCAUSE)) {
            case 0: {
                printf("Instruction address misaligned");
                break;
            }
            case 1: {
                printf("Instruction access fault");
                break;
            }
            case 2: {
                printf("Illegal instruction");
                break;
            }
            case 3: {
                printf("Breakpoint");
                break;
            }
            case 4: {
                printf("Load address misaligned");
                break;
            }
            case 5: {
                printf("Load access fault");
                break;
            }
            case 6: {
                printf("Store/AMO address misaligned");
                break;
            }
            case 7: {
                printf("Store/AMO access fault");
                break;
            }
            case 8: {
                printf("Environment call from U-mode or VU-mode");
                break;
            }
            case 9: {
                printf("Environment call from HS-mode");
                break;
            }
            case 10: {
                printf("Environment call from VS-mode");
                break;
            }
            case 11: {
                printf("Environment call from M-mode");
                break;
            }
            case 12: {
                printf("Instruction page fault");
                break;
            }
            case 13: {
                printf("Load page fault");
                break;
            }
            case 15: {
                printf("Store/AMO page fault");
                break;
            }
            case 20: {
                printf("Instruction guest-page fault");
                break;
            }
            case 21: {
                printf("Load guest-page fault");
                break;
            }
            case 22: {
                printf("Virtual instruction");
                break;
            }
            case 23: {
                printf("Store/AMO guest-page fault");
                break;
            }
            default: {
                printf("Unsupported exception");
            }
        }
    }
    printf("\n");
    printf("S-mode : panicked (scause = 0x%lx sepc = 0x%lx stval = 0x%lx)\n", csr_read(CSR_SCAUSE) , csr_read(CSR_SEPC), csr_read(CSR_STVAL));
    panic();
}
