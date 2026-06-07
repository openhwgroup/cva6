#define LEVEL0 0x0
#define LEVEL1 0x1
#define LEVEL2 0x2

#define sv32 0x00
#define sv39 0x01






#define INIT_SIGNATURE(SIG_LBL) ;\
    LA x2, SIG_LBL

#if XLEN == 64
#define SIG_UPDATE(SIG_REG) ;\
    sd SIG_REG, 0(x2)       ;\
    addi x2, x2, 8
#else
#define SIG_UPDATE(SIG_REG) ;\
    sw SIG_REG, 0(x2)       ;\
    addi x2, x2, 4          
#endif

    
#define SV32_ENABLE(root_lbl)         ;\
    li   t0, (1 << 31)                ;\
    LA   t1, root_lbl                 ;\
    srli t1, t1, 12                   ;\
    or   t0, t0, t1                   ;\
    csrw satp, t0                     ;\
    sfence.vma

#define SV39_ENABLE(root_lbl)         ;\
    li   t0, (8 << 60)                ;\
    LA   t1, root_lbl                 ;\
    srli t1, t1, 12                   ;\
    or   t0, t0, t1                   ;\
    csrw satp, t0                     ;\
    sfence.vma
    
#if XLEN == 64
#define SVADU_ENABLE_HW_AD()          ;\
    li   t0, (1 << 61)                ;\
    csrrs zero, menvcfg, t0
#else
#define SVADU_ENABLE_HW_AD()          ;\
    li   t0, (1 << 29)                ;\
    csrrs zero, menvcfgh, t0
#endif



#define PTE_SETUP_RV32_Sv32(_PAR, _PR, _TR0, _TR1, VA, level)  	;\
    srli _PAR, _PAR, 12                                         ;\
    slli _PAR, _PAR, 10                                         ;\
    or _PAR, _PAR, _PR                                          ;\
    .if (level==1)                                              ;\
        LA(_TR1, rvtest_Sroot_pg_tbl)                           ;\
        .set vpn, ((VA>>22)&0x3FF)<<2                           ;\
    .endif                                                      ;\
    .if (level==0)                                              ;\
        LA(_TR1, rvtest_slvl0_pg_tbl)                           ;\
        .set vpn, ((VA>>12)&0x3FF)<<2                           ;\
    .endif                                                      ;\
    LI(_TR0, vpn)                                               ;\
    add _TR1, _TR1, _TR0                                        ;\
    SREG _PAR, 0(_TR1);      



#define PTE_SETUP_RV64(PA_REG, PERMS_REG, TR0, TR1, VA, PTE_LEVEL, MODE) ;\
    srli PA_REG, PA_REG, 12                                              ;\
    slli PA_REG, PA_REG, 10                                              ;\
    or PA_REG, PA_REG, PERMS_REG                                         ;\
    .if(MODE == sv39)                                                    ;\
        .if(PTE_LEVEL == 2)                                              ;\
            LA(TR1, rvtest_Sroot_pg_tbl)                                 ;\
            .set vpn, ((VA >> 30) & 0x1FF) << 3                          ;\
        .endif                                                           ;\
        .if(PTE_LEVEL == 1)                                              ;\
            LA(TR1, rvtest_slvl1_pg_tbl)                                 ;\
            .set vpn, ((VA >> 21) & 0x1FF) << 3                          ;\
        .endif                                                           ;\
        .if(PTE_LEVEL == 0)                                              ;\
            LA(TR1, rvtest_slvl0_pg_tbl)                                 ;\
            .set vpn, ((VA >> 12) & 0x1FF) << 3                          ;\
        .endif                                                           ;\
    .endif                                                               ;\
    LI(TR0, vpn)                                                         ;\
    add TR1, TR1, TR0                                                    ;\
    SREG PA_REG, 0(TR1)                                                  ;

/* ============================================================
 * PMP helpers
 * ============================================================ */
#define PMP_OPEN_ALL()               ;\
    li   t0, -1                      ;\
    csrw pmpaddr0, t0                ;\
    li   t0, 0x1f                    ;\
    csrw pmpcfg0, t0





#define PTE_SETUP_SV32(PA_LBL, PERMS, VA, level)            ;\
    LA(a0, PA_LBL)                                          ;\
    LI(a1, PERMS)                                           ;\
    PTE_SETUP_RV32_Sv32(a0, a1, t0, t1, VA, level)          ;


#define SUPERPAGE_PTE_SETUP_SV32(PA_LBL, PERMS, VA, level)  ;\
    LA(a0, (PA_LBL))                                        ;\
    srli a0, a0, 22                                         ;\
    slli a0, a0, 22                                         ;\
    LI(a1, PERMS)                                           ;\
    PTE_SETUP_RV32_Sv32(a0, a1, t0, t1, VA, level)          ;


#define PTE_SETUP_SV39(PA_LBL, PERMS, VA, PTE_LEVEL)        ;\
    LA(a0, PA_LBL)                                          ;\
    LI(a1, PERMS)                                           ;\
    PTE_SETUP_RV64(a0, a1, t0, t1, VA, PTE_LEVEL, sv39)     ;

    
#define SUPERPAGE_PTE_SETUP_SV39(PA_LBL, PERMS, VA, PTE_LEVEL)  ;\
    .set PA_SHIFT, (PTE_LEVEL*9) + 12                           ;\
    LA(a0, (PA_LBL))                                            ;\
    srli a0, a0, PA_SHIFT                                       ;\
    slli a0, a0, PA_SHIFT                                       ;\
    LI(a1, PERMS)                                               ;\
    PTE_SETUP_RV64(a0, a1, t0, t1, VA, PTE_LEVEL, sv39)         ;

#define ENTER_SMODE(TEST_LBL)         ;\
    csrr t0, mstatus                  ;\
    li   t1, ~(3 << 11)               ;\
    and  t0, t0, t1                   ;\
    li   t1, (1 << 11)                ;\
    or   t0, t0, t1                   ;\
    csrw mstatus, t0                  ;\
    LA   t0, TEST_LBL                 ;\
    csrw mepc, t0                     ;\
    mret

#define ENTER_UMODE(TEST_LBL)         ;\
    csrr t0, mstatus                  ;\
    li   t1, ~(3 << 11)               ;\
    and  t0, t0, t1                   ;\
    csrw mstatus, t0                  ;\
    LA   t0, TEST_LBL                 ;\
    csrw mepc, t0                     ;\
    mret

#define RETURN_TO_MMODE(RETURN_LBL)   ;\
    LA   t0, RETURN_LBL               ;\
    csrw mepc, t0                     ;\
    csrr t0, mstatus                  ;\
    li   t1, ~(3 << 11)               ;\
    and  t0, t0, t1                   ;\
    li   t1, (3 << 11)                ;\
    or   t0, t0, t1                   ;\
    csrw mstatus, t0                  ;\
    mret



#if XLEN == 64
#define READ_PTE(REG, VA, PTE_LEVEL)                    ;\
    .if (PTE_LEVEL == 0)                                ;\
        LA   t0, rvtest_slvl0_pg_tbl                    ;\
        LI   t1, (((VA) >> 12) & 0x1FF) << 3            ;\
    .endif                                              ;\
    .if (PTE_LEVEL == 1)                                ;\
        LA   t0, rvtest_slvl1_pg_tbl                    ;\
        LI   t1, (((VA) >> 21) & 0x1FF) << 3            ;\
    .endif                                              ;\
    .if (PTE_LEVEL == 2)                                ;\
        LA   t0, rvtest_Sroot_pg_tbl                    ;\
        LI   t1, (((VA) >> 30) & 0x1FF) << 3            ;\
    .endif                                              ;\
    add  t0, t0, t1                                     ;\
    ld   REG, 0(t0)
#else
#define READ_PTE(REG, VA, PTE_LEVEL)                    ;\
    .if (PTE_LEVEL == 0)                                ;\
        LA   t0, rvtest_slvl0_pg_tbl                    ;\
        LI   t1, (((VA) >> 12) & 0x3FF) << 2            ;\
    .endif                                              ;\
    .if (PTE_LEVEL == 1)                                ;\
        LA   t0, rvtest_Sroot_pg_tbl                    ;\
        LI   t1, (((VA) >> 22) & 0x3FF) << 2            ;\
    .endif                                              ;\
    add   t0, t0, t1                                    ;\
    lw    REG, 0(t0)                                    
#endif

#define SIG_UPDATE_PTE(VA_R, VA_W, VA_X, VA_A, PTE_LEVEL)   ;\
    READ_PTE(a4, (VA_R), (PTE_LEVEL))                 ;\
    srli a4, a4, 6                                    ;\
    andi a4, a4, 0x1                                  ;\
    SIG_UPDATE(a4)                                    ;\
    li t0, 1                                          ;\
    bne a4, t0, fail                                  ;\
                                                        \
    READ_PTE(a4, (VA_W), (PTE_LEVEL))                 ;\
    srli a4, a4, 6                                    ;\
    andi a4, a4, 0x1                                  ;\
    SIG_UPDATE(a4)                                    ;\
    li t0, 1                                          ;\
    bne a4, t0, fail                                  ;\
                                                        \
    READ_PTE(a4, (VA_W), (PTE_LEVEL))                 ;\
    srli a4, a4, 7                                    ;\
    andi a4, a4, 0x1                                  ;\
    SIG_UPDATE(a4)                                    ;\
    li t0, 1                                          ;\
    bne a4, t0, fail                                  ;\
                                                        \
    READ_PTE(a4, (VA_A), (PTE_LEVEL))                 ;\
    srli a4, a4, 6                                    ;\
    andi a4, a4, 0x1                                  ;\
    SIG_UPDATE(a4)                                    ;\
    li t0, 1                                          ;\
    bne a4, t0, fail                                  ;\
                                                        \
    READ_PTE(a4, (VA_A), (PTE_LEVEL))                 ;\
    srli a4, a4, 7                                    ;\
    andi a4, a4, 0x1                                  ;\
    SIG_UPDATE(a4)                                    ;\
    li t0, 1                                          ;\
    bne a4, t0, fail                                  ;\
                                                        \
    READ_PTE(a4, (VA_X), (PTE_LEVEL))                 ;\
    srli a4, a4, 6                                    ;\
    andi a4, a4, 0x1                                  ;\
    SIG_UPDATE(a4)                                    ;\
    li t0, 1                                          ;\
    bne a4, t0, fail                                  ;