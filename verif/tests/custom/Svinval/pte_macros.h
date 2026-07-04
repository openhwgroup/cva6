#ifndef PTE_MACROS_H
#define PTE_MACROS_H

#ifndef XLEN
#error "XLEN is not defined. Compile with -DXLEN=64 or -DXLEN=32."
#endif

#if XLEN != 64 && XLEN != 32
#error "Unsupported XLEN value. Only XLEN=64 or XLEN=32 is supported."
#endif

#define LEVEL0 0x0
#define LEVEL1 0x1
#define LEVEL2 0x2

#define sv32 0x00
#define sv39 0x01

#define FAULT_SFENCE_W_INVAL   0x1
#define FAULT_SINVAL_VMA       0x2
#define FAULT_SFENCE_INVAL_IR  0x4
#define FAULT_SFENCE_VMA       0x8

#define EXPECT_NO_FAULT        0x0
#define EXPECT_SMODE_TVM       (FAULT_SINVAL_VMA | FAULT_SFENCE_VMA)
#define EXPECT_ALL_FAULT       0xf

/* ------------------------------------------------------------
 * SATP layout
 *
 * RV64 Sv39:
 *   satp.MODE = bits [63:60] = 8
 *   satp.ASID = bits [59:44]
 *   satp.PPN  = bits [43:0]
 *
 * RV32 Sv32:
 *   satp.MODE = bit [31] = 1
 *   satp.ASID = bits [30:22]
 *   satp.PPN  = bits [21:0]
 * ------------------------------------------------------------ */

#if XLEN == 64

#define TEST_SATP_MODE        0x8000000000000000  /* MODE=8, Sv39 */
#define TEST_SATP_ASID1       0x0000100000000000  /* ASID=1 << 44 */
#define TEST_SATP_ASID2       0x0000200000000000  /* ASID=2 << 44 */
#define SATP_ASID_SHIFT  44
#define SATP_ASID_MASK   0xffff

#else

#define TEST_SATP_MODE        0x80000000          /* MODE=1, Sv32 */
#define TEST_SATP_ASID1       0x00400000          /* ASID=1 << 22 */
#define TEST_SATP_ASID2       0x00800000          /* ASID=2 << 22 */
#define SATP_ASID_SHIFT  22
#define SATP_ASID_MASK   0x1ff

#endif

#define ASID1_VAL        0x1
#define ASID2_VAL        0x2

#define PTE_TABLE_FLAG   0x001
#define PTE_RWAD         0x0c7
#define PTE_RWXAD        0x0cf

/* ------------------------------------------------------------
 * Signature helpers
 * ------------------------------------------------------------ */

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

/* ------------------------------------------------------------
 * PMP
 * ------------------------------------------------------------ */

#define PMP_OPEN_ALL()               ;\
    li   t0, -1                      ;\
    csrw pmpaddr0, t0                ;\
    li   t0, 0x1f                    ;\
    csrw pmpcfg0, t0

/* ------------------------------------------------------------
 * Enable virtual memory
 * ------------------------------------------------------------ */

#if XLEN == 64

#define SV39_ENABLE(root_lbl)         ;\
    LA   t0, root_lbl                 ;\
    srli t0, t0, 12                   ;\
    li   t1, TEST_SATP_MODE                ;\
    or   t0, t0, t1                   ;\
    csrw satp, t0                     ;\
    sfence.vma x0, x0

#define VM_ENABLE(root_lbl)           ;\
    SV39_ENABLE(root_lbl)

#else

#define SV32_ENABLE(root_lbl)         ;\
    LA   t0, root_lbl                 ;\
    srli t0, t0, 12                   ;\
    li   t1, TEST_SATP_MODE                ;\
    or   t0, t0, t1                   ;\
    csrw satp, t0                     ;\
    sfence.vma x0, x0

#define VM_ENABLE(root_lbl)           ;\
    SV32_ENABLE(root_lbl)

#endif

/* ------------------------------------------------------------
 * TVM control
 * ------------------------------------------------------------ */

#define TVM_ENABLE()         ;\
    li   t0, MSTATUS_TVM     ;\
    csrs mstatus, t0

#define TVM_DISABLE()        ;\
    li   t0, MSTATUS_TVM     ;\
    csrc mstatus, t0

/* ------------------------------------------------------------
 * SATP ASID switch
 *
 * Important:
 *   Default SWITCH_ASID1/2 only writes satp.
 *   It does NOT automatically execute sfence.vma.
 *
 * Reason:
 *   In Svinval functional tests, automatically flushing during
 *   ASID switch can hide whether sinval.vma actually invalidated
 *   the target translation.
 *
 * Use SWITCH_ASID1_FENCE / SWITCH_ASID2_FENCE only when you really
 * want to serialize after changing satp.
 * ------------------------------------------------------------ */

#define SWITCH_ASID1()              ;\
    LA      t0, rvtest_Sroot_pg_tbl ;\
    srli    t0, t0, 12              ;\
    li      t1, TEST_SATP_MODE           ;\
    or      t0, t0, t1              ;\
    li      t1, TEST_SATP_ASID1          ;\
    or      t0, t0, t1              ;\
    csrw    satp, t0

#define SWITCH_ASID2()              ;\
    LA      t0, rvtest_Sroot_pg_tbl ;\
    srli    t0, t0, 12              ;\
    li      t1, TEST_SATP_MODE           ;\
    or      t0, t0, t1              ;\
    li      t1, TEST_SATP_ASID2          ;\
    or      t0, t0, t1              ;\
    csrw    satp, t0

#define SWITCH_ASID1_FENCE()        ;\
    SWITCH_ASID1()                  ;\
    sfence.vma x0, x0

#define SWITCH_ASID2_FENCE()        ;\
    SWITCH_ASID2()                  ;\
    sfence.vma x0, x0

/* ------------------------------------------------------------
 * SATP ASID debug checks
 * ------------------------------------------------------------ */

#define CHECK_SATP_ASID(EXPECTED_ASID, FAIL_LBL) ;\
    csrr    t3, satp                           ;\
    srli    t4, t3, SATP_ASID_SHIFT            ;\
    li      t5, SATP_ASID_MASK                 ;\
    and     t4, t4, t5                         ;\
    li      t5, EXPECTED_ASID                  ;\
    bne     t4, t5, FAIL_LBL

#define DUMP_SATP_AND_ASID()        ;\
    csrr    t3, satp                ;\
    SIG_UPDATE(t3)                  ;\
    srli    t4, t3, SATP_ASID_SHIFT ;\
    li      t5, SATP_ASID_MASK      ;\
    and     t4, t4, t5              ;\
    SIG_UPDATE(t4)

/* ------------------------------------------------------------
 * Svinval sequence
 * ------------------------------------------------------------ */

#define SINVAL_SEQ_VA_ALL_ASID(VA_REG) ;\
    .option push                       ;\
    .option arch, +svinval              ;\
    sfence.w.inval                     ;\
    sinval.vma VA_REG, x0              ;\
    sfence.inval.ir                    ;\
    .option pop

#define SINVAL_SEQ_VA_ASID(VA_REG, ASID_REG) ;\
    .option push                           ;\
    .option arch, +svinval                  ;\
    sfence.w.inval                         ;\
    sinval.vma VA_REG, ASID_REG            ;\
    sfence.inval.ir                        ;\
    .option pop

#define SINVAL_SEQ(VA_REG, ASID_REG) ;\
    .option push                   ;\
    .option arch, +svinval          ;\
    sfence.w.inval                  ;\
    sinval.vma VA_REG, ASID_REG     ;\
    sfence.inval.ir                 ;\
    .option pop

/* ------------------------------------------------------------
 * PTE update helpers
 * ------------------------------------------------------------ */

#if XLEN == 64

#define SET_L0_PTE(PTE_OFF, PA, FLAGS) ;\
    LA      t0, rvtest_slvl0_pg_tbl     ;\
    li      t1, PA                      ;\
    srli    t1, t1, 12                  ;\
    slli    t1, t1, 10                  ;\
    ori     t1, t1, FLAGS               ;\
    sd      t1, PTE_OFF(t0)

#else

#define SET_L0_PTE(PTE_OFF, PA, FLAGS) ;\
    LA      t0, rvtest_slvl0_pg_tbl     ;\
    li      t1, PA                      ;\
    srli    t1, t1, 12                  ;\
    slli    t1, t1, 10                  ;\
    ori     t1, t1, FLAGS               ;\
    sw      t1, PTE_OFF(t0)

#endif

#define SET_L0_RWAD_PTE(PTE_OFF, PA) ;\
    SET_L0_PTE(PTE_OFF, PA, PTE_RWAD)

/* ------------------------------------------------------------
 * Fault signature helper
 * ------------------------------------------------------------ */

#define SIG_UPDATE_FAULT(EXPECTED_MASK) ;\
    SIG_UPDATE(s11)                     ;\
    SIG_UPDATE(s10)                     ;\
    li t0, EXPECTED_MASK                ;\
    bne s11, t0, fail                   ;\
    bnez s10, fail

/* ------------------------------------------------------------
 * Load check helpers
 * ------------------------------------------------------------ */

#if XLEN == 64

#define CHECK_LOAD_EQ(VA, EXPECTED, FAIL_LBL) ;\
    li      t0, VA                         ;\
    ld      t1, 0(t0)                      ;\
    li      t2, EXPECTED                   ;\
    bne     t1, t2, FAIL_LBL

#define CHECK_LOAD_OLD_OR_NEW(VA, OLD_VAL, NEW_VAL, FAIL_LBL) ;\
    li      t0, VA                                      ;\
    ld      t1, 0(t0)                                   ;\
    li      t2, OLD_VAL                                 ;\
    beq     t1, t2, 1f                                  ;\
    li      t2, NEW_VAL                                 ;\
    beq     t1, t2, 1f                                  ;\
    j       FAIL_LBL                                    ;\
1:

#else

#define CHECK_LOAD_EQ(VA, EXPECTED, FAIL_LBL) ;\
    li      t0, VA                         ;\
    lw      t1, 0(t0)                      ;\
    li      t2, EXPECTED                   ;\
    bne     t1, t2, FAIL_LBL

#define CHECK_LOAD_OLD_OR_NEW(VA, OLD_VAL, NEW_VAL, FAIL_LBL) ;\
    li      t0, VA                                      ;\
    lw      t1, 0(t0)                                   ;\
    li      t2, OLD_VAL                                 ;\
    beq     t1, t2, 1f                                  ;\
    li      t2, NEW_VAL                                 ;\
    beq     t1, t2, 1f                                  ;\
    j       FAIL_LBL                                    ;\
1:

#endif

#define RECORD_TEST_PASS(TEST_ID) ;\
    li      a0, TEST_ID       ;\
    SIG_UPDATE(a0)

#endif /* PTE_MACROS_H */