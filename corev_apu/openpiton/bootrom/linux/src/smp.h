#pragma once

// The hart that non-SMP tests should run on
#ifndef NONSMP_HART
#define NONSMP_HART 0
#endif

// The maximum number of HARTs this code supports
//#define CLINT_CTRL_ADDR 0xFFF1020000
// Barrier on the cacheline above the stack pointer
#define SMP_BARRIER_ADDR (0x84000000 + 64)
#ifndef MAX_HARTS
#define MAX_HARTS 2
#endif
//#define CLINT_END_HART_IPI CLINT_CTRL_ADDR + (MAX_HARTS * 4)

/* If your test needs to temporarily block multiple-threads, do this:
 *    smp_pause(reg1, reg2)
 *    ... single-threaded work ...
 *    smp_resume(reg1, reg2)
 *    ... multi-threaded work ...
 */

#define smp_pause(reg1, reg2) \
    li reg1, NONSMP_HART;     \
    csrr reg2, mhartid;       \
    bne reg1, reg2, 42f

#define smp_resume(reg1, reg2)   \
    42:;                         \
    li reg1, SMP_BARRIER_ADDR;   \
    lw reg2, 0(reg1);            \
    csrr reg1, mhartid;          \
    bne reg1, reg2, 42b;         \
    li reg1, SMP_BARRIER_ADDR;   \
    addi reg2, reg2, 1;          \
    amoswap.w reg1, reg2, (reg1);\
    43:;                         \
    li reg1, SMP_BARRIER_ADDR;   \
    lw reg2, 0(reg1);            \
    li reg1, MAX_HARTS;          \
    bne reg1, reg2, 43b
