#include "pte_macros.h"
#include "model_test.h"
#include "arch_test.h"
#include "encoding.h"

#define NUM_TEST 2

/* ===================================================================================================================
 * TEST CASE  (Svinval ACT-style privilege/decode test)
 *
 * This test follows the official ACT-style Svinval privilege behavior:
 *
 * 1. Execute sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma in S-mode.
 *    Expected: No fault
 *
 * 2. Execute sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma in U-mode.
 *    Expected: 4 Illegal instruction exceptions
 *
 * Expected signature:
 *   Test 1:
 *     s11 = 0x0
 *     s10 = 0x0
 *
 *   Test 2:
 *     s11 = 0xf
 *     s10 = 0x0
 * =================================================================================================================== */

.set MMODE, 3
.set SMODE, 1
.set UMODE, 0


// ===================================================================================================================
// Enter lower privilege mode and start act_fence_test
// ===================================================================================================================
.macro ACT_FENCE_PROCESS MODE
    csrr t0, mstatus

    // Clear MPP
    li   t1, ~(3 << 11)
    and  t0, t0, t1

    .if \MODE == SMODE
        // MPP = S-mode
        li   t1, (1 << 11)
    .elseif \MODE == UMODE
        // MPP = U-mode
        li   t1, 0
    .else
        .error "Unsupported privilege mode for ACT Svinval test"
    .endif

    or   t0, t0, t1
    csrw mstatus, t0

    LA   t0, act_fence_test
    csrw mepc, t0
    mret
.endm


.macro ACT_SINVAL_TEST_RUNNER MODE, test_pass
    TVM_DISABLE()

    LA   t0, trap_handler
    csrw mtvec, t0

    LA   t0, \test_pass
    csrw mscratch, t0

    ACT_FENCE_PROCESS \MODE
.endm


.section .text.init
.global rvtest_entry_point
rvtest_entry_point:
    RVMODEL_BOOT

RVTEST_CODE_BEGIN

    INIT_SIGNATURE(signature)
    PMP_OPEN_ALL()

    // ---------------------------------------------------------------------------------------------------------------
    // TEST 1: S-mode
    // sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma should not trap.
    // ---------------------------------------------------------------------------------------------------------------
    ACT_SINVAL_TEST_RUNNER SMODE, test1_pass

test1_pass:
    SIG_UPDATE_FAULT(EXPECT_NO_FAULT)

    // ---------------------------------------------------------------------------------------------------------------
    // TEST 2: U-mode
    // sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma should all trap as illegal instructions.
    // ---------------------------------------------------------------------------------------------------------------
    ACT_SINVAL_TEST_RUNNER UMODE, test2_pass

test2_pass:
    SIG_UPDATE_FAULT(EXPECT_ALL_FAULT)

    j pass


// ===================================================================================================================
// Common test body executed in S-mode or U-mode
// ===================================================================================================================
act_fence_test:
    // s11: observed illegal-instruction fault mask
    // s10: unexpected trap flag
    li s11, 0
    li s10, 0

    .option push
    .option arch, +svinval

    // ---------------------------------------------------------------------------------------------------------------
    // sfence.w.inval
    // ---------------------------------------------------------------------------------------------------------------
    li t6, FAULT_SFENCE_W_INVAL
    LA t5, 1f
    sfence.w.inval
1:
    nop

    // ---------------------------------------------------------------------------------------------------------------
    // sinval.vma x0, x0
    // ---------------------------------------------------------------------------------------------------------------
    li t6, FAULT_SINVAL_VMA
    LA t5, 2f
    sinval.vma x0, x0
2:
    nop

    // ---------------------------------------------------------------------------------------------------------------
    // sfence.inval.ir
    // ---------------------------------------------------------------------------------------------------------------
    li t6, FAULT_SFENCE_INVAL_IR
    LA t5, 3f
    sfence.inval.ir
3:
    nop

    // ---------------------------------------------------------------------------------------------------------------
    // sfence.vma x0, x0
    // ---------------------------------------------------------------------------------------------------------------
    li t6, FAULT_SFENCE_VMA
    LA t5, 4f
    sfence.vma x0, x0
4:
    nop

    .option pop

    ecall


// ===================================================================================================================
// Trap handler
// ===================================================================================================================
    .balign 4
trap_handler:
    csrr t0, mcause

    // Illegal instruction
    li t1, 2
    beq t0, t1, trap_illegal

    // U-mode ecall
    li t1, 8
    beq t0, t1, trap_from_ecall

    // S-mode ecall
    li t1, 9
    beq t0, t1, trap_from_ecall

    // M-mode ecall
    li t1, 11
    beq t0, t1, trap_from_ecall

    // Unexpected trap
    li s10, 1
    li s11, 0xdead
    j return_to_mmode_pass_label


trap_illegal:
    // Record which instruction trapped.
    // t6 contains FAULT_* bit.
    or   s11, s11, t6

    // Skip the trapped instruction.
    // t5 contains the resume label after the instruction.
    csrw mepc, t5
    mret


trap_from_ecall:
    j return_to_mmode_pass_label


return_to_mmode_pass_label:
    // Return to test1_pass or test2_pass in M-mode.
    csrr t0, mscratch
    csrw mepc, t0

    csrr t1, mstatus

    // Clear MPP
    li   t2, ~(3 << 11)
    and  t1, t1, t2

    // Set MPP = M-mode
    li   t2,  (3 << 11)
    or   t1, t1, t2

    csrw mstatus, t1
    mret


// ===================================================================================================================
// Test end points
// ===================================================================================================================
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


// ===================================================================================================================
// Signature
// ===================================================================================================================
RVTEST_SIG_BEGIN

#if XLEN == 64
.align 3
signature:
    .fill NUM_TEST*4, 8, 0
#else
.align 2
signature:
    .fill NUM_TEST*4, 4, 0
#endif

RVTEST_SIG_END


// ===================================================================================================================
// Host interface
// ===================================================================================================================
.align 6
.global tohost
.global fromhost

#if XLEN == 64
tohost:
    .dword 0
fromhost:
    .dword 0
#else
tohost:
    .word 0
fromhost:
    .word 0
#endif