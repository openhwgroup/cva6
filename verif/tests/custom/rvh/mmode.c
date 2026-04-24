#include <stdio.h>

#include "mmode.h"
#include "call.h"
#include "csr.h"
#include "trampoline.h"
#include "sbi.h"
#include "utils.h"

__thread struct trap_context* __tc;

__attribute__((naked, aligned(4))) void mvec(void) {
    SAVE_CONTEXT();
    printf("M-mode : panicked (mcause = 0x%lx mepc = 0x%lx mstatus = 0x%lx)\n", csr_read(CSR_MCAUSE), csr_read(CSR_MEPC), csr_read(CSR_MSTATUS));
    panic();
}

void firmware_init(void) {
    csr_write(CSR_MTVEC, (uint64_t)&mvec);
    csr_clear(CSR_MSTATUS, SR_MPP | SR_FS | SR_VS | SR_XS | SR_MPRV);
    csr_set(CSR_MSTATUS, SR_MPP_S | SR_FS_INITIAL | SR_VS_INITIAL | SR_XS_INITIAL); // SR_SXL_64 SR_UXL_64 SR_MPRV
    csr_write(CSR_MENVCFG, ENVCFG_CBIE | ENVCFG_CBCFE | ENVCFG_CBZE);
    csr_write(CSR_MIE, 0ul);
    csr_write(CSR_PMPADDR0, ~0ul);
    csr_write(CSR_MEDELEG,
                  bit(EXC_INST_MISALIGNED) | bit(EXC_INST_ACCESS) | bit(EXC_INST_ILLEGAL) | bit(EXC_BREAKPOINT) | bit(EXC_LOAD_MISALIGNED) | bit(EXC_LOAD_ACCESS) |
                  bit(EXC_STORE_MISALIGNED) | bit(EXC_STORE_ACCESS) | bit(EXC_U_VU_SYSCALL) | bit(EXC_VS_SYSCALL) | bit(EXC_INST_PAGE_FAULT) |
                  bit(EXC_LOAD_PAGE_FAULT) | bit(EXC_STORE_PAGE_FAULT) | bit(EXC_INST_GUEST_PAGE_FAULT) | bit(EXC_LOAD_GUEST_PAGE_FAULT) |
                  bit(EXC_VIRTUAL_INST_FAULT) | bit(EXC_STORE_GUEST_PAGE_FAULT));
    csr_write(CSR_MIDELEG, bit(IRQ_S_SOFT) | bit(IRQ_S_TIMER) | bit(IRQ_S_EXT) | bit(IRQ_S_GEXT) | bit(IRQ_VS_SOFT) | bit(IRQ_VS_TIMER) | bit(IRQ_VS_EXT));
    csr_write(CSR_PMPCFG0, PMP_R | PMP_W | PMP_X | PMP_A_NAPOT);
    reset();

    csr_set(CSR_MIP, bit(IRQ_S_TIMER)); // so the timer interrupt test passes

    asm volatile("la a6, 1f\n"
                 "csrw mepc, a6" ::
                     : "memory", "a6");

    asm volatile("mret\n"
                 "1:\n");
}
