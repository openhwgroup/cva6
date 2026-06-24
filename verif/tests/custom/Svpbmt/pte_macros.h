#define LEVEL0 0x0
#define LEVEL1 0x1
#define LEVEL2 0x2

#define sv39 0x01

#define FAULT_STORE  0x1
#define FAULT_LOAD   0x2
#define FAULT_FETCH  0x4
#define FAULT_AMO    0x8

#define EXPECT_NO_FAULT      0x0
#define EXPECT_ALL_FAULT     0xF

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


#define SV39_ENABLE(root_lbl)         ;\
    li   t0, (8 << 60)                ;\
    LA   t1, root_lbl                 ;\
    srli t1, t1, 12                   ;\
    or   t0, t0, t1                   ;\
    csrw satp, t0                     ;\
    sfence.vma
    
#define SVPBMT_ENABLE()          ;\
    li   t0, (1 << 62)                 ;\
    csrrs zero, menvcfg, t0


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


#define PMP_OPEN_ALL()               ;\
    li   t0, -1                      ;\
    csrw pmpaddr0, t0                ;\
    li   t0, 0x1f                    ;\
    csrw pmpcfg0, t0


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


#define SIG_UPDATE_FAULT(EXPECTED_MASK) ;\
    SIG_UPDATE(s11)                     ;\
    SIG_UPDATE(s10)                     ;\
    li t0, EXPECTED_MASK                ;\
    bne s11, t0, fail                   ;\
    bnez s10, fail