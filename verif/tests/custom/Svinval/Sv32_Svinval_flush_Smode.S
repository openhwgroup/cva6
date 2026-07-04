#include "pte_macros.h"
#include "model_test.h"
#include "arch_test.h"
#include "encoding.h"

#define NUM_TEST 4

#if XLEN != 32
#error "This test is for RV32/Sv32 only"
#endif

/* ===================================================================================================================
 * TEST CASE         (Svinval privilege (S-mode) / Sv32 page-table translation flush test)
 *
 * Assumption:
 *   - Execute this test in S-mode with mstatus.TVM = 0.
 *   - Sv32 page table is used.
 *   - Each Svinval sequence is:
 *       sfence.w.inval -> sinval.vma rs1, rs2 -> sfence.inval.ir
 *
 * 1. Basic target invalidation
 *    VA_A + ASID1: OLD PTE -> NEW PTE, then sinval.vma VA_A, ASID1.
 *
 * 2. All VA entries for one ASID
 *    VA_A/VA_B under ASID1: OLD PTEs -> NEW PTEs, then sinval.vma x0, ASID1.
 *
 * 3. One VA entry across all ASIDs
 *    VA_A under ASID1/ASID2: OLD PTE -> NEW PTE, then sinval.vma VA_A, x0.
 *
 * 4. Full translation invalidation
 *    VA_A/VA_B across ASIDs: OLD PTEs -> NEW PTEs, then sinval.vma x0, x0.
 * =================================================================================================================== */

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

    // Sv32 virtual addresses
    // VA_A = 0x40000000: VPN[1] = 0x100, VPN[0] = 0x000
    // VA_B = 0x40010000: VPN[1] = 0x100, VPN[0] = 0x010
    .set VA_A, 0x40000000
    .set VA_B, 0x40010000

    // Physical addresses in the 0x80000000 DRAM region
    .set PA_ID,     0x80000000
    .set PA_A_OLD,  0x80020000
    .set PA_A_NEW,  0x80022000
    .set PA_B_OLD,  0x80021000
    .set PA_B_NEW,  0x80023000

    // 32-bit test values for RV32
    .set VAL_A_OLD, 0x11112222
    .set VAL_A_NEW, 0x9999aaaa
    .set VAL_B_OLD, 0x55556666
    .set VAL_B_NEW, 0xaaaabbbb

    // Sv32 PTE size is 4 bytes.
    // VA_B VPN[0] = 0x10, so PTE_B_OFF = 0x10 * 4 = 0x40.
    .set PTE_A_OFF, 0x000
    .set PTE_B_OFF, 0x040

    PMP_OPEN_ALL()

    call init_memory

    // Enable Sv32 before entering S-mode
    SV32_ENABLE(rvtest_Sroot_pg_tbl)

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


////////////////////////////////////////////////////////////////////////////////////
// TEST 1: Basic target invalidation
////////////////////////////////////////////////////////////////////////////////////
test1:
    call reset_mapping
    SWITCH_ASID1()

    CHECK_LOAD_EQ(VA_A, VAL_A_OLD, fail)

    SET_L0_PTE(PTE_A_OFF, PA_A_NEW, PTE_RWAD)
    fence rw, rw

    li s1, VA_A
    li s2, ASID1_VAL
    SINVAL_SEQ(s1, s2)

    CHECK_LOAD_EQ(VA_A, VAL_A_NEW, fail)

    .align 2
    ecall


////////////////////////////////////////////////////////////////////////////////////
// TEST 2: All VA entries for one ASID
////////////////////////////////////////////////////////////////////////////////////
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


////////////////////////////////////////////////////////////////////////////////////
// TEST 3: One VA entry across all ASIDs
////////////////////////////////////////////////////////////////////////////////////
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


////////////////////////////////////////////////////////////////////////////////////
// TEST 4: Full translation invalidation
////////////////////////////////////////////////////////////////////////////////////
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


.option pop


////////////////////////////////////////////////////////////////////////////////////
// Sv32 memory/page-table initialization
////////////////////////////////////////////////////////////////////////////////////
init_memory:
    mv      s0, ra

    LA      a0, rvtest_Sroot_pg_tbl
    call    clear_page

    LA      a0, rvtest_slvl0_pg_tbl
    call    clear_page

    // Sv32 root[0x100] -> level0 table for VA_A / VA_B region.
    LA      t0, rvtest_Sroot_pg_tbl
    LA      t1, rvtest_slvl0_pg_tbl
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, PTE_TABLE_FLAG
    sw      t1, 0x400(t0)

    // Sv32 root[0x200] -> 4 MiB identity mapping for 0x80000000 region.
    li      t1, PA_ID
    srli    t1, t1, 12
    slli    t1, t1, 10
    ori     t1, t1, PTE_RWXAD

    li      t2, 0x800
    add     t2, t0, t2
    sw      t1, 0(t2)

    call    reset_mapping

    mv      ra, s0
    ret


reset_mapping:
    SET_L0_PTE(PTE_A_OFF, PA_A_OLD, PTE_RWAD)
    SET_L0_PTE(PTE_B_OFF, PA_B_OLD, PTE_RWAD)

    li      t0, PA_A_OLD
    li      t1, VAL_A_OLD
    sw      t1, 0(t0)

    li      t0, PA_A_NEW
    li      t1, VAL_A_NEW
    sw      t1, 0(t0)

    li      t0, PA_B_OLD
    li      t1, VAL_B_OLD
    sw      t1, 0(t0)

    li      t0, PA_B_NEW
    li      t1, VAL_B_NEW
    sw      t1, 0(t0)

    fence   rw, rw
    sfence.vma x0, x0
    ret


clear_page:
    li      t0, 4096
1:
    sw      x0, 0(a0)
    addi    a0, a0, 4
    addi    t0, t0, -4
    bnez    t0, 1b
    ret


    .balign 4
trap_handler:
    csrr t0, mcause

    li t1, 9                               // S-mode ecall
    beq t0, t1, test_complete_shortcut

    li t1, 13                              // Load page fault
    beq t0, t1, load_page_fault

    li t1, 12                              // Instruction page fault
    beq t0, t1, instruction_page_fault

    li t1, 15                              // Store page fault
    beq t0, t1, store_page_fault

    j unexpected_trap


test_complete_shortcut:
    csrr t0, mscratch
    csrw mepc, t0

    csrr t0, mstatus
    li   t1, ~(3 << 11)
    and  t0, t0, t1
    li   t1,  (3 << 11)                    // MPP = M-mode
    or   t0, t0, t1
    csrw mstatus, t0

    mret


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
    .balign 4
pass:
    LA      t0, tohost
    li      t1, 1
    sw      t1, 0(t0)
    j .

    .balign 4
fail:
    LA      t0, tohost
    li      t1, 3
    sw      t1, 0(t0)
    j .


RVTEST_CODE_END


RVTEST_DATA_BEGIN

.align 12
rvtest_Sroot_pg_tbl:
    .skip 4096

.align 12
rvtest_slvl0_pg_tbl:
    .skip 4096

RVTEST_DATA_END


RVTEST_SIG_BEGIN
.align 2
signature:
    .fill NUM_TEST*4, 4, 0
RVTEST_SIG_END


.align 6
.global tohost
.global fromhost
tohost:
    .word 0
fromhost:
    .word 0