#ifndef HMODE_TRAMPOLINE_H
#define HMODE_TRAMPOLINE_H

#include <stdint.h>

struct trap_context {
    /* Return address */
    /*   0 */ uint64_t ra;
    /* Global pointer */
    /*   1 */ uint64_t gp;
    /* Thread pointer */
    /*   2 */ uint64_t tp;
    /* Function arguments and return values */
    /*   3 */ uint64_t a0;
    /*   4 */ uint64_t a1;
    /*   5 */ uint64_t a2;
    /*   6 */ uint64_t a3;
    /*   7 */ uint64_t a4;
    /*   8 */ uint64_t a5;
    /*   9 */ uint64_t a6;
    /*  10 */ uint64_t a7;
    /* Temporaries and alternate link registers */
    /*  11 */ uint64_t t0;
    /*  12 */ uint64_t t1;
    /*  13 */ uint64_t t2;
    /*  14 */ uint64_t t3;
    /*  15 */ uint64_t t4;
    /*  16 */ uint64_t t5;
    /*  17 */ uint64_t t6;
    /* Saved registers */
    /*  19 */ uint64_t s0; /* Saved Frame pointer */
    /*  19 */ uint64_t s1;
    /*  20 */ uint64_t s2;
    /*  21 */ uint64_t s3;
    /*  22 */ uint64_t s4;
    /*  23 */ uint64_t s5;
    /*  24 */ uint64_t s6;
    /*  25 */ uint64_t s7;
    /*  26 */ uint64_t s8;
    /*  27 */ uint64_t s9;
    /*  28 */ uint64_t s10;
    /*  29 */ uint64_t s11;
} __attribute__((packed));

extern __thread struct trap_context* __tc;

#define SAVE_CONTEXT()                                \
    asm volatile("addi sp, sp, -256\n"                \
                 "sd ra,   0*8(sp)\n"                 \
                 "sd gp,   1*8(sp)\n"                 \
                 "sd tp,   2*8(sp)\n"                 \
                 "sd a0,   3*8(sp)\n"                 \
                 "sd a1,   4*8(sp)\n"                 \
                 "sd a2,   5*8(sp)\n"                 \
                 "sd a3,   6*8(sp)\n"                 \
                 "sd a4,   7*8(sp)\n"                 \
                 "sd a5,   8*8(sp)\n"                 \
                 "sd a6,   9*8(sp)\n"                 \
                 "sd a7,   10*8(sp)\n"                \
                 "sd t0,   11*8(sp)\n"                \
                 "sd t1,   12*8(sp)\n"                \
                 "sd t2,   13*8(sp)\n"                \
                 "sd t3,   14*8(sp)\n"                \
                 "sd t4,   15*8(sp)\n"                \
                 "sd t5,   16*8(sp)\n"                \
                 "sd t6,   17*8(sp)\n"                \
                 "sd s0,   18*8(sp)\n"                \
                 "sd s1,   19*8(sp)\n"                \
                 "sd s2,   20*8(sp)\n"                \
                 "sd s3,   21*8(sp)\n"                \
                 "sd s4,   22*8(sp)\n"                \
                 "sd s5,   23*8(sp)\n"                \
                 "sd s6,   24*8(sp)\n"                \
                 "sd s7,   25*8(sp)\n"                \
                 "sd s8,   26*8(sp)\n"                \
                 "sd s9,   27*8(sp)\n"                \
                 "sd s10,  28*8(sp)\n"                \
                 "sd s11,  29*8(sp)\n"                \
                 /* Store thread_context to TLS */    \
                 "lui a5,  %%tprel_hi(__tc)\n"        \
                 "add a5, a5, tp, %%tprel_add(__tc)\n"\
                 "sd sp,   %%tprel_lo(__tc)(a5)\n"    \
                 ::: "memory")

#define RESTORE_CONTEXT(ret)                          \
    asm volatile(/* Store thread_context to TLS */    \
                 "lui a5,  %%tprel_hi(__tc)\n"        \
                 "add a5, a5, tp, %%tprel_add(__tc)\n"\
                 "ld sp, %%tprel_lo(__tc)(a5)\n"      \
                 "ld ra,   0*8(sp)\n"                 \
                 "ld gp,   1*8(sp)\n"                 \
                 "ld tp,   2*8(sp)\n"                 \
                 "ld a0,   3*8(sp)\n"                 \
                 "ld a1,   4*8(sp)\n"                 \
                 "ld a2,   5*8(sp)\n"                 \
                 "ld a3,   6*8(sp)\n"                 \
                 "ld a4,   7*8(sp)\n"                 \
                 "ld a5,   8*8(sp)\n"                 \
                 "ld a6,   9*8(sp)\n"                 \
                 "ld a7,   10*8(sp)\n"                \
                 "ld t0,   11*8(sp)\n"                \
                 "ld t1,   12*8(sp)\n"                \
                 "ld t2,   13*8(sp)\n"                \
                 "ld t3,   14*8(sp)\n"                \
                 "ld t4,   15*8(sp)\n"                \
                 "ld t5,   16*8(sp)\n"                \
                 "ld t6,   17*8(sp)\n"                \
                 "ld s0,   18*8(sp)\n"                \
                 "ld s1,   19*8(sp)\n"                \
                 "ld s2,   20*8(sp)\n"                \
                 "ld s3,   21*8(sp)\n"                \
                 "ld s4,   22*8(sp)\n"                \
                 "ld s5,   23*8(sp)\n"                \
                 "ld s6,   24*8(sp)\n"                \
                 "ld s7,   25*8(sp)\n"                \
                 "ld s8,   26*8(sp)\n"                \
                 "ld s9,   27*8(sp)\n"                \
                 "ld s10,  28*8(sp)\n"                \
                 "ld s11,  29*8(sp)\n"                \
                 "addi sp, sp, 256\n"                 \
                 #ret ::: "memory")

#define GET_TRAP_CONTEXT() (__tc)

void test_ret(void);
void test_ecall(void);
extern uint64_t flag;

#define RV_INS_LEN(ins) ((((ins) & 0x3) != 0x3) ? 2 : ((((ins) & 0x1f) != 0x1f) ? 4 : ((((ins) & 0x3f) != 0x3f) ? 6 : 8)))

#define NEXT_INSTRUCTION(inst, n)                    \
    ({                                               \
        uint64_t __pc = (inst);                      \
        for (int i = 0; i < (n); i++) {              \
            __pc += RV_INS_LEN(*(uint8_t *)(__pc));  \
        };                                           \
        __pc;                                        \
    })


#endif //HMODE_TRAMPOLINE_H
