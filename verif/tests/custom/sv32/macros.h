#include "../env/encoding.h"

#define _start   rvtest_entry_point
#define SMODE_ECALL ecall
#define UMODE_ECALL ecall

#define LEVEL0 0x00
#define LEVEL1 0x01

#define SUPERPAGE_SHIFT 22

#define PTE(PA, PR)                                                ;\
    srli     PA, PA, RISCV_PGSHIFT                                 ;\
    slli     PA, PA, PTE_PPN_SHIFT                                 ;\
    or       PA, PA, PR                                            ;

#define PTE_SETUP_RV32(PA, PR, TMP, VA, PGTB_ADDR,LEVEL)           ;\
    PTE(PA, PR)                                                    ;\
    .if (LEVEL==1)                                                 ;\
        la   TMP, PGTB_ADDR                                        ;\
        srli VA,  VA, SUPERPAGE_SHIFT                              ;\
    .endif                                                         ;\
    .if (LEVEL==0)                                                 ;\
        la   TMP, PGTB_ADDR                                        ;\
        slli VA,  VA, PTE_PPN_SHIFT                                ;\
        srli VA,  VA, SUPERPAGE_SHIFT                              ;\
    .endif                                                         ;\
    slli     VA,  VA,  2                                           ;\
    add      TMP, TMP, VA                                          ;\
    sw     PA,  0(TMP)                                             ;

#define SATP_SETUP_SV32(PGTB_ADDR)                                 ;\
    la   t6,   PGTB_ADDR                                           ;\
    li   t5,   SATP32_MODE                                         ;\
    srli t6,   t6, RISCV_PGSHIFT                                   ;\
    or   t6,   t6, t5                                              ;\
    csrw satp, t6                                                  ;\
    sfence.vma                                                     ;

#define CHANGE_T0_S_MODE(MEPC_ADDR)                                ;\
    li        t0, MSTATUS_MPP                                      ;\
    csrc mstatus, t0                                               ;\
    li  t1, MSTATUS_MPP & ( MSTATUS_MPP >> 1)                      ;\
    csrs mstatus, t1                                               ;\
    csrw mepc, MEPC_ADDR                                           ;\
    mret                                                           ;

#define CHANGE_T0_U_MODE(MEPC_ADDR)                                ;\
    li        t0, MSTATUS_MPP                                      ;\
    csrc mstatus, t0                                               ;\
    csrw mepc, MEPC_ADDR                                           ;\
    mret                                                           ;


#define RVTEST_EXIT_LOGIC                                          ;\
exit:                                                              ;\
    add t1, zero, x1                                               ;\
    slli t1, t1, 1                                                 ;\
    addi t1, t1, 1                                                 ;\
    la t0, tohost                                                  ;\
    sw t1, 0(t0)                                                   ;\
    j exit                                                         ;

#define COREV_VERIF_EXIT_LOGIC                                     ;\
exit:                                                              ;\
    slli x1, x1, 1                                                 ;\
    addi x1, x1, 1                                                 ;\
    mv x30, s1                                                     ;\
    sw x1, tohost, x30                                             ;\
    self_loop: j self_loop                                         ;

#define ALL_MEM_PMP                                                ;\
    li t2, -1                                                      ;\
    csrw pmpaddr0, t2                                              ;\
    li t2, 0x0F	                                                   ;\
    csrw pmpcfg0, t2                                               ;\
    sfence.vma                                                     ;

#define TEST_PROLOG(ADDR,CAUSE)                                    ;\
    la t1, rvtest_check                                            ;\
    la t2, ADDR                                                    ;\
    li t3, CAUSE                                                   ;\
    li t4, 1                                                       ;\
    sw t4, 0(t1)                                                   ;\
    sw t2, 4(t1)                                                   ;\
    sw t3, 8(t1)                                                   ;\
    la a1,rvtest_data                                              ;

.macro INCREMENT_MEPC label_suffix                                 ;\
    csrr t1, mepc                                                  ;\
    lw t5, 0(t1)                                                   ;\
    li t2, 3                                                       ;\
    and t5, t5, t2                                                 ;\
    bne t2, t5, not_32_bit_Instr_\label_suffix                     ;\
    addi t1, t1, 4                                                 ;\
    j write_mepc_\label_suffix                                     ;\
    not_32_bit_Instr_\label_suffix:                                ;\
    addi t1, t1, 2                                                 ;\
    write_mepc_\label_suffix:                                      ;\
    csrw mepc, t1                                                  ;\
.endm                                                              ;

#define TEST_STATUS                                                ;\
    la a1, rvtest_check                                            ;\
    lw t1, 0(a1)                                                   ;\
    bne t1, x0, test_fail                                          ;
