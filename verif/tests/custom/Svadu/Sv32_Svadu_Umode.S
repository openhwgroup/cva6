#include "pte_macros.h"
#include "model_test.h"
#include "arch_test.h"
#include "encoding.h"

/* ===================================================================================================================
 * TEST CASE  
 * 1. PTE.A unset , PTE.D set   for three distinct leaf PTEs at level 1,   RWX permissions (read, write, execute page)
 * 2. PTE.A set   , PTE.D unset   for three distinct leaf PTEs at level 1,   RWX permissions (read, write, execute page)
 * 3. PTE.A unset , PTE.D unset for three distinct leaf PTEs at level 1,   RWX permissions (read, write, execute page)
 * 4. PTE.A unset , PTE.D set   for three distinct leaf PTEs at level 0,   RWX permissions (read, write, execute page)
 * 5. PTE.A set   , PTE.D unset   for three distinct leaf PTEs at level 0,   RWX permissions (read, write, execute page)
 * 6. PTE.A unset , PTE.D unset for three distinct leaf PTEs at level 0,   RWX permissions (read, write, execute page)
 * =================================================================================================================== */
#define NUM_TEST 6

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
 * Run one Svadu RWX test case
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
.macro Sv32_SVADU_TEST_RUNNER VA_W, VA_R, VA_X, VA_A, level, test_pass

    /* Compute page-aligned virtual base for the selected page level */
    .set VA_SHIFT, (\level*10) + 12
    LI( a0, ((\VA_W >> VA_SHIFT) << VA_SHIFT))
    LI( a1, ((\VA_R >> VA_SHIFT) << VA_SHIFT))
    LI( a5, ((\VA_X >> VA_SHIFT) << VA_SHIFT))
    LI( a7, ((\VA_A >> VA_SHIFT) << VA_SHIFT))

    /* Extract the page offset of rvtest_data within the selected page size */
    LA( t0, rvtest_data)
    slli t0, t0, 32-VA_SHIFT
    srli t0, t0, 32-VA_SHIFT

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

    /* ============================================================
     * Map the test code region as an executable supervisor page.
     * A and D are already set so instruction fetch from the test code
     * does not participate in the Svadu A/D-bit update check.
     * ============================================================ */
    SUPERPAGE_PTE_SETUP_SV32(rvtest_code_begin, (PTE_D | PTE_A | PTE_U | PTE_X | PTE_R | PTE_V), va_rvtest_code_begin, LEVEL1)

    // ================================================ Sv32 & Svadu SETUP ============================================== //
    
    SV32_ENABLE(rvtest_Sroot_pg_tbl)   /* Enable Sv32 translation with root page table */
    
    SVADU_ENABLE_HW_AD()               /* Enable hardware A/D-bit update mode */
    
    PMP_OPEN_ALL()                     /* Open PMP to avoid PMP-related access faults */
    

    // ============================================= TEST CASE. 1 ======================================================= //
    // PTE.A unset , PTE.D set   for three distinct leaf PTEs at level 1,   RWX permissions (read, write, execute page)   //
    // ================================================================================================================== //
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_D | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_w, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_D | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_r, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_D | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_x, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_D | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_a, LEVEL1)

    sfence.vma

    Sv32_SVADU_TEST_RUNNER va_data_l1_w, va_data_l1_r, va_data_l1_x, va_data_l1_a, LEVEL1, test1_pass

test1_pass:
    SIG_UPDATE_PTE(va_data_l1_r, va_data_l1_w, va_data_l1_x, va_data_l1_a, LEVEL1)

    // ============================================= TEST CASE. 2 ======================================================= //
    // PTE.A set , PTE.D unset   for three distinct leaf PTEs at level 1,   RWX permissions (read, write, execute page)   //
    // ================================================================================================================== //
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_w, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_r, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_x, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_a, LEVEL1)

    sfence.vma

    Sv32_SVADU_TEST_RUNNER va_data_l1_w, va_data_l1_r, va_data_l1_x, va_data_l1_a, LEVEL1, test2_pass

test2_pass:
    SIG_UPDATE_PTE(va_data_l1_r, va_data_l1_w, va_data_l1_x, va_data_l1_a, LEVEL1)


    // ============================================= TEST CASE. 3 ======================================================= //
    // PTE.A unset , PTE.D unset   for three distinct leaf PTEs at level 1,   RWX permissions (read, write, execute page) //
    // ================================================================================================================== //
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_w, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_r, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_x, LEVEL1)
    SUPERPAGE_PTE_SETUP_SV32(rvtest_data, (PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l1_a, LEVEL1)

    sfence.vma

    Sv32_SVADU_TEST_RUNNER va_data_l1_w, va_data_l1_r, va_data_l1_x, va_data_l1_a, LEVEL1, test3_pass

test3_pass:
    SIG_UPDATE_PTE(va_data_l1_r, va_data_l1_w, va_data_l1_x, va_data_l1_a, LEVEL1)

    // ============================================= TEST CASE. 4 ======================================================= //
    // PTE.A unset , PTE.D set   for three distinct leaf PTEs at level 0,   RWX permissions (read, write, execute page) //
    // ================================================================================================================== //
    LA t0, rvtest_Sroot_pg_tbl
    lw t1, 0(t0)
    SIG_UPDATE(t1)

    LA t0, rvtest_slvl0_pg_tbl
    lw t1, 8(t0)        // VA 0x2000의 L0 PTE
    SIG_UPDATE(t1)


    PTE_SETUP_SV32(rvtest_slvl0_pg_tbl, (PTE_V), va_data_l0_w, LEVEL1)
    PTE_SETUP_SV32(rvtest_data, (PTE_D | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_w, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_D | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_r, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_D | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_x, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_D | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_a, LEVEL0)

    sfence.vma

    Sv32_SVADU_TEST_RUNNER va_data_l0_w, va_data_l0_r, va_data_l0_x, va_data_l0_a, LEVEL0, test4_pass

test4_pass:
    SIG_UPDATE_PTE(va_data_l0_r, va_data_l0_w, va_data_l0_x, va_data_l0_a, LEVEL0)


    // ============================================= TEST CASE. 5 ======================================================= //
    // PTE.A set , PTE.D unset   for three distinct leaf PTEs at level 0,   RWX permissions (read, write, execute page) //
    // ================================================================================================================== //
    PTE_SETUP_SV32(rvtest_slvl0_pg_tbl, (PTE_V), va_data_l0_w, LEVEL1)
    PTE_SETUP_SV32(rvtest_data, (PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_w, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_r, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_x, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_A | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_a, LEVEL0)

    sfence.vma

    Sv32_SVADU_TEST_RUNNER va_data_l0_w, va_data_l0_r, va_data_l0_x, va_data_l0_a, LEVEL0, test5_pass

test5_pass:
    SIG_UPDATE_PTE(va_data_l0_r, va_data_l0_w, va_data_l0_x, va_data_l0_a, LEVEL0)


    // ============================================= TEST CASE. 6 ======================================================= //
    // PTE.A unset , PTE.D unset   for three distinct leaf PTEs at level 0,   RWX permissions (read, write, execute page) //
    // ================================================================================================================== //
    PTE_SETUP_SV32(rvtest_slvl0_pg_tbl, (PTE_V), va_data_l0_w, LEVEL1)
    PTE_SETUP_SV32(rvtest_data, (PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_w, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_r, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_x, LEVEL0)
    PTE_SETUP_SV32(rvtest_data, (PTE_U | PTE_X | PTE_W | PTE_R | PTE_V), va_data_l0_a, LEVEL0)

    sfence.vma

    Sv32_SVADU_TEST_RUNNER va_data_l0_w, va_data_l0_r, va_data_l0_x, va_data_l0_a, LEVEL0, test6_pass

test6_pass:
    SIG_UPDATE_PTE(va_data_l0_r, va_data_l0_w, va_data_l0_x, va_data_l0_a, LEVEL0)
    j pass          /* TEST END POINT */



rwax_test:
    /* Load access  -> checks/updates A-bit    */
    lw a3, 20(a1)    

    /* Store access -> checks/updates A/D-bits */
    li a2, 0x800     
    sw a2, 20(a0)   

    /* AMO access -> checks/updates A/D-bits */
    addi t0, a7, 20         
    li t1, 1
    amoadd.w t2, t1, (t0)   

    /* Fetch access -> checks/updates A-bits   */
    jalr ra, a5, 0   
    .align 2         /* align ecall to avoid RVC halfword issue */
    ecall            /* Finish test and trap back to S-mode     */


trap_handler:
    csrr t0, mcause                        /* Read trap cause */

    li t1, 8                               /* U-mode ecall    */
    beq t0, t1, test_complete_shortcut     /* If trap occurs by supervisor_ecall, then test passes */

    li t1, 13                              /* Load page fault */
    beq t0, t1, load_page_fault
    li t1, 12                              /* Instruction page fault */
    beq t0, t1, instruction_page_fault
    li t1, 15                              /* Store page fault */
    beq t0, t1, store_page_fault

    j unexpected_trap                      /* Unexpected fault */


test_complete_shortcut:
    csrr t0, mscratch                      /* Load next test label (e.g., test1_pass, test2_pass ..) */
    csrw mepc, t0                          /* Return to test_pass label for signature memory */

    csrr t0, mstatus                    
    li   t1, (3 << 11)
    or   t0, t0, t1
    csrw mstatus, t0

    mret                                   /* Return to M-mode continuation */


instruction_page_fault:
    LA t0, tohost
    li t1, 3
    sw t1, 0(t0)
    j .

load_page_fault:
    LA t0, tohost
    li t1, 3
    sw t1, 0(t0)
    j .

store_page_fault:
    LA t0, tohost
    li t1, 3
    sw t1, 0(t0)
    j .

unexpected_trap:
    LA t0, tohost
    li t1, 3
    sw t1, 0(t0)
    j .

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
    .fill NUM_TEST*4, 4, 0
RVTEST_SIG_END

.align 6
.global tohost
.global fromhost
tohost:
    .dword 0
fromhost:
    .dword 0