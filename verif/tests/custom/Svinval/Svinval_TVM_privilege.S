#include "pte_macros.h"
#include "model_test.h"
#include "arch_test.h"
#include "encoding.h"

#define NUM_TEST 6

/* ===================================================================================================================
 * TEST CASE  (Svinval privilege / TVM decode test)
  * 1. mstatus.TVM = 0, execute sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma in M-mode
 *    --->  required: No fault
 * 2. mstatus.TVM = 1, execute sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma in M-mode
 *    --->  required: No fault
 * 3. mstatus.TVM = 0, execute sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma in S-mode
 *    --->  required: No fault
 * 4. mstatus.TVM = 1, execute sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma in S-mode
 *    --->  required: 2 Illegal insruction exceptions (sinval.vma, sfence.vma)
 * 5. mstatus.TVM = 0, execute sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma in U-mode
 *    --->  required: 4 Illegal instruction execptions (All)
 * 6. mstatus.TVM = 1, execute sfence.w.inval, sinval.vma, sfence.inval.ir, sfence.vma in U-mode
 *    --->  required: 4 Illegal instruction execptions (All)
 * =================================================================================================================== */
.set MMODE, 3
.set SMODE, 1
.set UMODE, 0


.macro FENCE_PROCESS MODE
    csrr t0, mstatus
    li   t1, ~(3 << 11)
    and  t0, t0, t1

    .if \MODE == MMODE
        li   t1, (3 << 11)     // MPP = M-mode

    .elseif \MODE == SMODE
        li   t1, (1 << 11)     // MPP = S-mode

    .elseif \MODE == UMODE
        li   t1, 0             // MPP = U-mode

    .else 
        .error "Unsupported privilege mode"
    .endif
    
    or   t0, t0, t1
    csrw mstatus, t0

    LA   t0, fence_test
    csrw mepc, t0
    mret
.endm

.macro SINVAL_TEST_RUNNER MODE, TVM, test_pass
    .if (\TVM == 0)
        TVM_DISABLE() 
    .elseif (\TVM == 1)
        TVM_ENABLE()
    .else 
        .error "Unsupported TVM value"
    .endif

    LA   t0, trap_handler
    csrw mtvec, t0

    LA   t0, \test_pass
    csrw mscratch, t0

    FENCE_PROCESS \MODE
.endm


.section .text.init
.global rvtest_entry_point
rvtest_entry_point:
    RVMODEL_BOOT

RVTEST_CODE_BEGIN
    INIT_SIGNATURE(signature)
    PMP_OPEN_ALL()

    // TEST 1
    SINVAL_TEST_RUNNER MMODE, 0, test_pass1

test_pass1:
    SIG_UPDATE_FAULT(EXPECT_NO_FAULT)
    
    // TEST 2
    SINVAL_TEST_RUNNER MMODE, 1, test_pass2

test_pass2:
    SIG_UPDATE_FAULT(EXPECT_NO_FAULT)

    // TEST 3
    SINVAL_TEST_RUNNER SMODE, 0, test_pass3

test_pass3:
    SIG_UPDATE_FAULT(EXPECT_NO_FAULT)

    // TEST 4
    SINVAL_TEST_RUNNER SMODE, 1, test_pass4

test_pass4:
    SIG_UPDATE_FAULT(EXPECT_SMODE_TVM)

    // TEST 5
    SINVAL_TEST_RUNNER UMODE, 0, test_pass5

test_pass5:
    SIG_UPDATE_FAULT(EXPECT_ALL_FAULT)

    // TEST 6
    SINVAL_TEST_RUNNER UMODE, 1, test_pass6

test_pass6:
    SIG_UPDATE_FAULT(EXPECT_ALL_FAULT)
    j pass


fence_test:
    li s11, 0
    li s10, 0

    .option push
    .option arch, +svinval

    // sfence.w.inval
    li t6, FAULT_SFENCE_W_INVAL
    LA t5, 1f
    sfence.w.inval
1:

    // sinval.vma
    li t6, FAULT_SINVAL_VMA
    LA t5, 2f
    sinval.vma x0, x0
2:

    // sfence.inval.ir
    li t6, FAULT_SFENCE_INVAL_IR
    LA t5, 3f
    sfence.inval.ir
3:

    // sfence.vma
    li t6, FAULT_SFENCE_VMA
    LA t5, 4f
    sfence.vma x0, x0
4:
    .option pop
    ecall
    .balign 4



trap_handler:
    csrr t0, mcause

    li t1, 2                  // illegal instruction
    beq t0, t1, trap_illegal

    li t1, 8                  // U-mode ecall
    beq t0, t1, trap_from_ecall

    li t1, 9                  // S-mode ecall
    beq t0, t1, trap_from_ecall

    li t1, 11                 // M-mode ecall
    beq t0, t1, trap_from_ecall

    // unexpected trap
    li s10, 1
    li s11, 0xdead
    csrr t0, mscratch
    csrw mepc, t0

    csrr t1, mstatus
    li   t2, ~(3 << 11)
    and  t1, t1, t2
    li   t2,  (3 << 11)
    or   t1, t1, t2
    csrw mstatus, t1
    mret

trap_from_ecall:
    csrr t0, mscratch
    csrw mepc, t0

    csrr t1, mstatus
    li   t2, ~(3 << 11)
    and  t1, t1, t2
    li   t2,  (3 << 11)
    or   t1, t1, t2
    csrw mstatus, t1

    mret

trap_illegal:
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