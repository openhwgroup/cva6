#include "pte_macros.h"
#include "model_test.h"
#include "arch_test.h"
#include "encoding.h"

#define NUM_TEST 4

/* ===================================================================================================================
 * TEST CASE         (Svinval privilege (S-mode) / Page-table translation flush test)
 *
 * Assumption:
 *   - Execute this test in S-mode with mstatus.TVM = 0.
 *   - Each Svinval sequence is:
 *       sfence.w.inval -> sinval.vma rs1, rs2 -> sfence.inval.ir
 *
 * 1. Basic target invalidation
 *    Fill VA_A + ASID1 translation with OLD PTE, then update the PTE to point to NEW PA.
 *    Execute sinval.vma VA_A, ASID1; VA_A must observe NEW value after the invalidation sequence.
 *
 * 2. All VA entries for one ASID
 *    Fill multiple translations under ASID1, then update their PTEs from OLD to NEW.
 *    Execute sinval.vma x0, ASID1; all cached translations belonging to ASID1 must observe NEW values.
 *
 * 3. One VA entry across all ASIDs
 *    Fill VA_A translations under ASID1 and ASID2, then update VA_A's PTE from OLD to NEW.
 *    Execute sinval.vma VA_A, x0; VA_A translations across ASIDs must observe NEW values.
 *
 * 4. Full translation invalidation
 *    Fill several translations across different VAs and ASIDs, then update all corresponding PTEs from OLD to NEW.
 *    Execute sinval.vma x0, x0; all cached translations must be invalidated and all reloads must observe NEW values.
 *
 =================================================================================================================== */

.macro ENTER_SMODE_FLUSH_TEST test_entry, test_pass
    TVM_DISABLE()

    LA   t0, trap_handler
    csrw mtvec, t0

    LA   t0, \test_pass
    csrw mscratch, t0

    csrr t0, mstatus
    li   t1, ~(3 << 11)
    and  t0, t0, t1
    li   t1,  (1 << 11)     // MPP = S-mode
    or   t0, t0, t1
    csrw mstatus, t0

    LA   t0, \test_entry
    csrw mepc, t0
    mret
.endm

.section .text.init
.global rvtest_entry_point
rvtest_entry_point:
    RVMODEL_BOOT

RVTEST_CODE_BEGIN
    INIT_SIGNATURE(signature)
    .option push
    .option arch, +svinval


    .set VA_A, 0x0000000040000000
    .set VA_B, 0x0000000040010000
    .set PA_ID,     0x0000000080000000
    .set PA_A_OLD,  0x0000000080020000
    .set PA_A_NEW,  0x0000000080022000
    .set PA_B_OLD,  0x0000000080021000
    .set PA_B_NEW,  0x0000000080023000

    .set VAL_A_OLD, 0x1111222233334444
    .set VAL_A_NEW, 0x9999aaaabbbbcccc
    .set VAL_B_OLD, 0x5555666677778888
    .set VAL_B_NEW, 0xaaaabbbbccccdddd

    .set PTE_A_OFF, 0x000
    .set PTE_B_OFF, 0x080


    PMP_OPEN_ALL()

    call init_memory

    // Enable Sv39 with ASID1 before entering S-mode
    SV39_ENABLE(rvtest_Sroot_pg_tbl)

    ENTER_SMODE_FLUSH_TEST test1, test1_pass

test1_pass:
    RECORD_TEST_PASS(1)


    ENTER_SMODE_FLUSH_TEST test2, test2_pass

test2_pass:
    RECORD_TEST_PASS(2)

    ENTER_SMODE_FLUSH_TEST test3, test3_pass

test3_pass:
    RECORD_TEST_PASS(3)

    ENTER_SMODE_FLUSH_TEST test4, test4_pass

test4_pass:
    RECORD_TEST_PASS(4)
    j pass


.option push
.option arch, +svinval


////////////////////////////////////////////////////////////////////////////////////
test1:
    call reset_mapping
    SWITCH_ASID1()

    csrr t3, satp
    SIG_UPDATE(t3)

    srli t4, t3, 44
    li   t5, 0xffff
    and  t4, t4, t5
    SIG_UPDATE(t4)

    li   t5, 1
    bne  t4, t5, fail

    CHECK_LOAD_EQ(VA_A, VAL_A_OLD, fail)

/* test1:
    call reset_mapping
    SWITCH_ASID1()

    CHECK_LOAD_EQ(VA_A, VAL_A_OLD, fail)

    SET_L0_PTE(PTE_A_OFF, PA_A_NEW, PTE_RWAD)
    fence rw, rw


    li s1, VA_A
    li s2, ASID1_VAL
    SINVAL_SEQ(s1, s2)
    CHECK_LOAD_EQ(VA_A, VAL_A_NEW, fail)
    j pass

    .align 2
    ecall
*/
// ===================================================================================================================
// TEST 2: All VA entries for one ASID
// Fill VA_A and VA_B under ASID1, then update both PTEs to NEW.
// Execute sinval.vma x0, ASID1; both VA_A and VA_B under ASID1 must observe NEW.
// ===================================================================================================================
test2:
    call reset_mapping
    SWITCH_ASID1()

    CHECK_LOAD_EQ(VA_A, VAL_A_OLD, fail)
    CHECK_LOAD_EQ(VA_B, VAL_B_OLD, fail)

    SET_L0_PTE(PTE_A_OFF, PA_A_NEW, PTE_RWAD)
    SET_L0_PTE(PTE_B_OFF, PA_B_NEW, PTE_RWAD)
    fence rw, rw

    li s2, ASID1_VAL
    SINVAL_SEQ(x0, s2)

    CHECK_LOAD_EQ(VA_A, VAL_A_NEW, fail)
    CHECK_LOAD_EQ(VA_B, VAL_B_NEW, fail)
    .align 2
    ecall

// ===================================================================================================================
// TEST 3: One VA entry across all ASIDs
// Fill VA_A under ASID1 and ASID2, then update VA_A PTE to NEW.
// Execute sinval.vma VA_A, x0; VA_A under both ASIDs must observe NEW.
// ===================================================================================================================
test3:
    call reset_mapping

    SWITCH_ASID1()
    CHECK_LOAD_EQ(VA_A, VAL_A_OLD, fail)

    SWITCH_ASID2()
    CHECK_LOAD_EQ(VA_A, VAL_A_OLD, fail)

    SET_L0_PTE(PTE_A_OFF, PA_A_NEW, PTE_RWAD)
    fence rw, rw

    li s1, VA_A
    SINVAL_SEQ(s1, x0)

    SWITCH_ASID1()
    CHECK_LOAD_EQ(VA_A, VAL_A_NEW, fail)

    SWITCH_ASID2()
    CHECK_LOAD_EQ(VA_A, VAL_A_NEW, fail)
    .align 2
    ecall

// ===================================================================================================================
// TEST 4: Full translation invalidation
// Fill several translations across VAs and ASIDs, then update all PTEs to NEW.
// Execute sinval.vma x0, x0; all reloads must observe NEW.
// ===================================================================================================================
test4:
    call reset_mapping

    SWITCH_ASID1()
    CHECK_LOAD_EQ(VA_A, VAL_A_OLD, fail)
    CHECK_LOAD_EQ(VA_B, VAL_B_OLD, fail)

    SWITCH_ASID2()
    CHECK_LOAD_EQ(VA_A, VAL_A_OLD, fail)

    SET_L0_PTE(PTE_A_OFF, PA_A_NEW, PTE_RWAD)
    SET_L0_PTE(PTE_B_OFF, PA_B_NEW, PTE_RWAD)
    fence rw, rw

    SINVAL_SEQ(x0, x0)

    SWITCH_ASID1()
    CHECK_LOAD_EQ(VA_A, VAL_A_NEW, fail)
    CHECK_LOAD_EQ(VA_B, VAL_B_NEW, fail)

    SWITCH_ASID2()
    CHECK_LOAD_EQ(VA_A, VAL_A_NEW, fail)
    .align 2
    ecall


init_memory:
    mv      s0, ra

    LA      a0, rvtest_Sroot_pg_tbl
    call    clear_page
    LA      a0, rvtest_slvl1_pg_tbl
    call    clear_page
    LA      a0, rvtest_slvl0_pg_tbl
    call    clear_page

    // root[1] -> level1 table for VA_A / VA_B region: 0x40000000
    LA      t0, rvtest_Sroot_pg_tbl
    LA      t1, rvtest_slvl1_pg_tbl
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, PTE_TABLE_FLAG
    sd      t1, 8(t0)

    // root[2] -> 1GiB identity mapping for code/data/page-table region: 0x80000000
    li      t1, PA_ID
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, PTE_RWXAD
    sd      t1, 16(t0)

    // level1[0] -> level0 table
    LA      t0, rvtest_slvl1_pg_tbl
    LA      t1, rvtest_slvl0_pg_tbl
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, PTE_TABLE_FLAG
    sd      t1, 0(t0)

    call    reset_mapping

    mv      ra, s0
    ret


reset_mapping:
    SET_L0_PTE(PTE_A_OFF, PA_A_OLD, PTE_RWAD)
    SET_L0_PTE(PTE_B_OFF, PA_B_OLD, PTE_RWAD)

    li      t0, PA_A_OLD
    li      t1, VAL_A_OLD
    sd      t1, 0(t0)

    li      t0, PA_A_NEW
    li      t1, VAL_A_NEW
    sd      t1, 0(t0)

    li      t0, PA_B_OLD
    li      t1, VAL_B_OLD
    sd      t1, 0(t0)

    li      t0, PA_B_NEW
    li      t1, VAL_B_NEW
    sd      t1, 0(t0)

    fence   rw, rw
    sfence.vma x0, x0
    ret


clear_page:
    li      t0, 4096
1:
    sd      x0, 0(a0)
    addi    a0, a0, 8
    addi    t0, t0, -8
    bnez    t0, 1b
    ret

    .balign 4
trap_handler:
    csrr t0, mcause                        /* Read trap cause */

    li t1, 9                               /* S-mode ecall    */
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