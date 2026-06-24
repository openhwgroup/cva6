#include "pte_macros.h"
#include "model_test.h"
#include "arch_test.h"
#include "encoding.h"

#define NUM_TEST 9

/* ===================================================================================================================
 * TEST CASE  (U-mode)
 * 1. Setup a PTE at level 2 with PBMT=1, RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: No fault
 * 2. Setup a PTE at level 2 with PBMT=2, RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: No fault
 * 3. Setup a PTE at level 2 with PBMT=3 (reserved encoding), RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: Store, load & fetch page fault
 * 4. Setup a PTE at level 1 with PBMT=1, RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: No fault
 * 5. Setup a PTE at level 1 with PBMT=2, RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: No fault
 * 6. Setup a PTE at level 1 with PBMT=3 (reserved encoding), RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: Store, load & fetch page fault
 * 7. Setup a PTE at level 0 with PBMT=1, RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: No fault
 * 8. Setup a PTE at level 0 with PBMT=2, RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: No fault
 * 9. Setup a PTE at level 0 with PBMT=3 (reserved encoding), RWX permissions given:
 *         Then, in S-Mode, the page is accessed --> required: Store, load & fetch page fault
 * =================================================================================================================== */

/* ======================================================
 * Enter to U-MODE and Jump to "rwax_test"
 *  
 *  Flow  
 *   1. Clear MPP field in mstatus
 *   2. Set MPP = 00 (User mode)
 *   3. Set mepc to "rwax_test" entry point
 *   4. Execute mret to enter U-mode
 *
 *  Result:
 *    - CPU transitions from M-mode -> U-mode
 *    - Start execution at "rwax_test"
 * ====================================================== */
.macro RWAX_PROCESS
    csrr t0, mstatus                  
    li   t1, ~(3 << 11)               
    and  t0, t0, t1                   
    csrw mstatus, t0                  
    LA   t0, rwax_test                 
    csrw mepc, t0                     
    mret
.endm

/* ============================================================
 * Run one Svadu RWAX test case
 *
 *  Flow:
 *   1. Build virtual addresses for write/read/fetch accesses.
 *   2. Preserve the offset of rvtest_data within the target page.
 *   3. Install the trap handler.
 *   4. Save the return label for this test case in mscratch.
 *   5. Enter the target privilege mode through RWAX_PROCESS.
 *
 *  Register usage:
 *   a0 = VA for store test
 *   a1 = VA for load test
 *   a5 = VA for instruction fetch test
 * ============================================================ */
.macro Sv39_SVPBMT_TEST_RUNNER VA_W, VA_R, VA_X, VA_A, level, test_pass

    /* Compute page-aligned virtual base for the selected page level */
    .set VA_SHIFT, (\level*9) + 12
    LI( a0, ((\VA_W >> VA_SHIFT) << VA_SHIFT))
    LI( a1, ((\VA_R >> VA_SHIFT) << VA_SHIFT))
    LI( a5, ((\VA_X >> VA_SHIFT) << VA_SHIFT))
    LI( a7, ((\VA_A >> VA_SHIFT) << VA_SHIFT))

    /* Extract the page offset of rvtest_data within the selected page size */
    LA( t0, rvtest_data)
    slli t0, t0, 64-VA_SHIFT
    srli t0, t0, 64-VA_SHIFT

    /* Add the same page offset so each VA points to rvtest_data */
    add a0, a0, t0
    add a1, a1, t0
    add a5, a5, t0
    add a7, a7, t0

    /* Install trap handler for exceptions/ecall during the test */
    LA   t0, trap_handler
    csrw mtvec, t0

    /* Save the continuation label after this test completes */
    LA   t0, \test_pass
    csrw mscratch, t0

    /* Enter U-MODE and execute rwax_test */
    RWAX_PROCESS

.endm

.section .text.init
.global rvtest_entry_point
rvtest_entry_point:
    RVMODEL_BOOT

RVTEST_CODE_BEGIN

    // ==================================== SIGNATURE & VIRTUAL ADDRESS SETUP ================================== //
     /* Initialize the signature region used to record PTE results */
    INIT_SIGNATURE(signature)

    /* Virtual addresses for Level-2 leaf PTE tests */
    .set va_data_l2_w,          0x040000000  // Store test VA
    .set va_data_l2_r,          0x0C0000000  // Load  test VA
    .set va_data_l2_x,          0x100000000  // Fetch test VA
    .set va_data_l2_a,          0x200000000  // AMO   test VA

    /* Virtual addresses for Level-1 leaf PTE tests */
    .set va_data_l1_w,          0x000200000  // Store test VA
    .set va_data_l1_r,          0x000400000  // Load  test VA
    .set va_data_l1_x,          0x000600000  // Fetch test VA
    .set va_data_l1_a,          0x000800000  // AMO   test VA

    /* Virtual addresses for Level-0 leaf PTE tests */
    .set va_data_l0_w,          0x000001000  // Store test VA
    .set va_data_l0_r,          0x000002000  // Load  test VA
    .set va_data_l0_x,          0x000003000  // Fetch test VA
    .set va_data_l0_a,          0x000004000  // AMO   test VA

    /* Virtual address used to map the test code itself */
    .set va_rvtest_code_begin,  0x80000000
    
    SUPERPAGE_PTE_SETUP_SV39(rvtest_code_begin, (PTE_D | PTE_A | PTE_U | PTE_X | PTE_R | PTE_V), va_rvtest_code_begin, LEVEL2)

    // ================================================ Sv39 & Svpbmt SETUP ============================================== //

    SV39_ENABLE(rvtest_Sroot_pg_tbl)   /* Enable Sv39 translation with root page table */
    
    SVPBMT_ENABLE()                    /* Enable Page-based Memory Attributes (Svpbmt) */

    PMP_OPEN_ALL()                     /* Open PMP to avoid PMP-related access faults */

    // ============================================= TEST CASE. 1 ======================================================= //
    // PBMT = 2'b01 (Non-cacheable) for three distinct leaf PTEs at level 2,   RWAX permissions (RD, WR, Atomic, EX)      //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 2) && (TEST_PBMT == 1) 
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_w, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_r, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_x, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_a, LEVEL2)

        sfence.vma

        Sv39_SVPBMT_TEST_RUNNER va_data_l2_w, va_data_l2_r, va_data_l2_x, va_data_l2_a, LEVEL2, test1_pass

    test1_pass:
        SIG_UPDATE_FAULT(EXPECT_NO_FAULT)
        j pass
    #endif


    // ============================================= TEST CASE. 2 ======================================================= //
    // PBMT = 2'b10 (I/O) for three distinct leaf PTEs at level 2,   RWAX permissions (RD, WR, Atomic, EX)                //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 2) && (TEST_PBMT == 2) 
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_w, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_r, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_x, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_a, LEVEL2)

        sfence.vma

        Sv39_SVPBMT_TEST_RUNNER va_data_l2_w, va_data_l2_r, va_data_l2_x, va_data_l2_a, LEVEL2, test2_pass

    test2_pass:
        SIG_UPDATE_FAULT(EXPECT_NO_FAULT)
        j pass
    #endif


    // ============================================= TEST CASE. 3 ======================================================= //
    // PBMT = 2'b11 (Reserved) for three distinct leaf PTEs at level 2,   RWAX permissions (RD, WR, Atomic, EX)           //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 2) && (TEST_PBMT == 3) 
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_w, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_r, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_x, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l2_a, LEVEL2)

        sfence.vma

        Sv39_SVPBMT_TEST_RUNNER va_data_l2_w, va_data_l2_r, va_data_l2_x, va_data_l2_a, LEVEL2, test3_pass

    test3_pass:
        SIG_UPDATE_FAULT(EXPECT_ALL_FAULT)
        j pass
    #endif


    // ============================================= TEST CASE. 4 ======================================================= //
    // PBMT = 2'b01 (Uncacheable) for three distinct leaf PTEs at level 1,   RWAX permissions (RD, WR, Atomic, EX)        //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 1) && (TEST_PBMT == 1) 
        PTE_SETUP_SV39(rvtest_slvl1_pg_tbl, (PTE_V), va_data_l1_w, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_w, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_r, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_x, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_a, LEVEL1)

        sfence.vma

        Sv39_SVPBMT_TEST_RUNNER va_data_l1_w, va_data_l1_r, va_data_l1_x, va_data_l1_a, LEVEL1, test4_pass

    test4_pass:
        SIG_UPDATE_FAULT(EXPECT_NO_FAULT)
        j pass
    #endif

    // ============================================= TEST CASE. 5 ======================================================= //
    // PBMT = 2'b10 (I/O) for three distinct leaf PTEs at level 1,   RWAX permissions (RD, WR, Atomic, EX)               //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 1) && (TEST_PBMT == 2) 
        PTE_SETUP_SV39(rvtest_slvl1_pg_tbl, (PTE_V), va_data_l1_w, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_w, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_r, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_x, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_a, LEVEL1)

        sfence.vma

        Sv39_SVPBMT_TEST_RUNNER va_data_l1_w, va_data_l1_r, va_data_l1_x, va_data_l1_a, LEVEL1, test5_pass

    test5_pass:
        SIG_UPDATE_FAULT(EXPECT_NO_FAULT)
        j pass
    #endif

    // ============================================= TEST CASE. 6 ======================================================= //
    // PBMT = 2'b11 (Reserved) for three distinct leaf PTEs at level 1,   RWAX permissions (RD, WR, Atomic, EX)           //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 1) && (TEST_PBMT == 3) 
        PTE_SETUP_SV39(rvtest_slvl1_pg_tbl, (PTE_V), va_data_l1_w, LEVEL2)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_w, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_r, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_x, LEVEL1)
        SUPERPAGE_PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_a, LEVEL1)

        sfence.vma

        Sv39_SVPBMT_TEST_RUNNER va_data_l1_w, va_data_l1_r, va_data_l1_x, va_data_l1_a, LEVEL1, test6_pass

    test6_pass:
        SIG_UPDATE_FAULT(EXPECT_ALL_FAULT)
        j pass
    #endif


    // ============================================= TEST CASE. 7 ======================================================= //
    // PBMT = 2'b01 (Uncacheable) for three distinct leaf PTEs at level 0,   RWAX permissions (RD, WR, Atomic, EX)        //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 0) && (TEST_PBMT == 1) 
        PTE_SETUP_SV39(rvtest_slvl1_pg_tbl, (PTE_V), va_data_l0_w, LEVEL2)
        PTE_SETUP_SV39(rvtest_slvl0_pg_tbl, (PTE_V), va_data_l0_w, LEVEL1)
        PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_w, LEVEL0)
        PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_r, LEVEL0)
        PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_x, LEVEL0)
        PTE_SETUP_SV39(rvtest_data, ((1 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_a, LEVEL0)

        sfence.vma

        Sv39_SVPBMT_TEST_RUNNER va_data_l0_w, va_data_l0_r, va_data_l0_x, va_data_l0_a, LEVEL0, test7_pass

    test7_pass:
        SIG_UPDATE_FAULT(EXPECT_NO_FAULT)
        j pass
    #endif


    // ============================================= TEST CASE. 8 ======================================================= //
    // PBMT = 2'b10 (I/O) for three distinct leaf PTEs at level 0,   RWAX permissions (RD, WR, Atomic, EX)                //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 0) && (TEST_PBMT == 2) 
        PTE_SETUP_SV39(rvtest_slvl1_pg_tbl, (PTE_V), va_data_l0_w, LEVEL2)
        PTE_SETUP_SV39(rvtest_slvl0_pg_tbl, (PTE_V), va_data_l0_w, LEVEL1)
        PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_w, LEVEL0)
        PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_r, LEVEL0)
        PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_x, LEVEL0)
        PTE_SETUP_SV39(rvtest_data, ((2 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_a, LEVEL0)

        sfence.vma

        Sv39_SVPBMT_TEST_RUNNER va_data_l0_w, va_data_l0_r, va_data_l0_x, va_data_l0_a, LEVEL0, test8_pass

    test8_pass:
        SIG_UPDATE_FAULT(EXPECT_NO_FAULT)
        j pass
    #endif


    // ============================================= TEST CASE. 9 ======================================================= //
    // PBMT = 2'b11 (Reserved) for three distinct leaf PTEs at level 0,  RWAX permissions (RD, WR, Atomic, EX)            //
    // ================================================================================================================== //
    #if (TEST_LEVEL == 0) && (TEST_PBMT == 3) 
    PTE_SETUP_SV39(rvtest_slvl1_pg_tbl, (PTE_V), va_data_l0_w, LEVEL2)
    PTE_SETUP_SV39(rvtest_slvl0_pg_tbl, (PTE_V), va_data_l0_w, LEVEL1)
    PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_w, LEVEL0)
    PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_r, LEVEL0)
    PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_x, LEVEL0)
    PTE_SETUP_SV39(rvtest_data, ((3 << 61) | PTE_D | PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_a, LEVEL0)

    sfence.vma

    Sv39_SVPBMT_TEST_RUNNER va_data_l0_w, va_data_l0_r, va_data_l0_x, va_data_l0_a, LEVEL0, test9_pass

test9_pass:
    SIG_UPDATE_FAULT(EXPECT_ALL_FAULT)
    j pass

    #endif


rwax_test:
    li s11, 0          // fault_mask = 0
    li s10, 0          // bad_cause = 0, optional

    // -------------------------
    // Store access
    // -------------------------
    li t6, FAULT_STORE
    LA t5, 1f
    li a2, 0x12345678
    sw a2, 20(a0)
1:

    // -------------------------
    // Load access
    // -------------------------
    li t6, FAULT_LOAD
    LA t5, 2f
    lw a3, 20(a1)
2:

    // -------------------------
    // AMO access
    // -------------------------
    li t6, FAULT_AMO
    LA t5, 3f
    li t0, 1
    addi t1, a7, 16
    amoadd.w a6, t0, (t1)
3:

    // -------------------------
    // Fetch access
    // -------------------------
    li t6, FAULT_FETCH
    LA t5, 4f
    jalr ra, a5, 0
4:

    ecall
    .balign 4



trap_handler:
    csrr t0, mcause

    // U-mode ecall = 8
    li t1, 8
    beq t0, t1, trap_from_ecall

    // Store/AMO page fault = 15
    li t1, 15
    beq t0, t1, trap_store_or_amo_fault

    // Load page fault = 13
    li t1, 13
    beq t0, t1, trap_load_fault

    // Instruction page fault = 12
    li t1, 12
    beq t0, t1, trap_fetch_fault

    // Unexpected trap cause
    li s10, 1
    csrw mepc, t5
    mret

trap_from_ecall:
    csrr t0, mscratch
    csrw mepc, t0

    // Return to M-mode before running test_pass / signature / tohost
    csrr t1, mstatus
    li   t2, ~(3 << 11)
    and  t1, t1, t2
    li   t2,  (3 << 11)
    or   t1, t1, t2
    csrw mstatus, t1

    mret

trap_store_or_amo_fault:
    li t1, FAULT_STORE
    beq t6, t1, 1f
    li t1, FAULT_AMO
    beq t6, t1, 1f
    li s10, 1
1:
    or s11, s11, t6
    csrw mepc, t5
    mret

trap_load_fault:
    li t1, FAULT_LOAD
    beq t6, t1, 1f
    li s10, 1
1:
    or s11, s11, t6
    csrw mepc, t5
    mret

trap_fetch_fault:
    li t1, FAULT_FETCH
    beq t6, t1, 1f
    li s10, 1
1:
    or s11, s11, t6
    csrw mepc, t5
    mret


/* TEST END POINT */
pass:
    LA      t0, tohost
    li      t1, 1
    sw      t1, 0(t0)
    j .

fail:
    LA      t0, tohost
    li      t1, 3
    sw      t1, 0(t0)
    j .
    
RVTEST_CODE_END


RVTEST_DATA_BEGIN
.align 12
rvtest_data:
    nop
    addi a4, a2, 4
    jr ra
    nop 
    .word 0xbeefcaf1
    .word 0xbeefcaf2
    jr ra


// Page Tables
.align 12
rvtest_Sroot_pg_tbl:
    .skip 4096

.align 12
rvtest_slvl0_pg_tbl:
    .skip 4096

.align 12
rvtest_slvl1_pg_tbl:
    .skip 4096

RVTEST_DATA_END

RVTEST_SIG_BEGIN
.align 3
signature:
    .fill NUM_TEST*4, 8, 0
RVTEST_SIG_END

.align 6
.global tohost
.global fromhost
tohost:
    .dword 0
fromhost:
    .dword 0