#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

#define TIMER_REG_ADDR         ((volatile uint32_t *) 0x15000000)  
#define TIMER_VAL_ADDR         ((volatile uint32_t *) 0x15000004) 

void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay) {
    *TIMER_REG_ADDR = mask;
    *TIMER_VAL_ADDR = 1 + cycle_delay;
}

void enable_interrupts() {
    asm("csrw mie,%0" : : "r"(0x1 << 16 | 0x1 << 17));
    asm("csrs mstatus,%0" : : "r"(0x1 << 3));
}

void m_fast0_irq_handler(void) {
    asm("addi x18,x18,1");
    asm("mret");
}

void m_fast1_irq_handler(void) {
    asm("addi x15,x15,1");
    asm("mret");
}

int main() {
    printf("In branch zero test\n");

    // Enable interrupt 16
    enable_interrupts();
    unsigned int a = 0x12345678;
    unsigned int b = 0x12345678;

    // --------------------------------------
    // beq
    // --------------------------------------
    printf("Test BEQ to zero offset\n");
    mm_ram_assert_irq(0x1 << 16, 100);
    __asm__
    (
        "li x18, %0\n"
        "li x19, %1\n"
        "1:\n"
        "beq x18,x19,1b\n"
        :
        : "i"(a), "i"(b)
        : "x18", "x19"
    );


    // --------------------------------------
    // bne
    // --------------------------------------
    printf("Test BNE to zero offset\n");
    mm_ram_assert_irq(0x1 << 16, 100);
    __asm__
    (
        "li x18, %0\n"
        "li x19, %1\n"
        "1:\n"
        "bne x18,x19,1b\n"
        :
        : "i"(a), "i"(b+1)
        : "x18", "x19"
    );

    // --------------------------------------
    // blt
    // --------------------------------------
    printf("Test BLT to zero offset\n");
    mm_ram_assert_irq(0x1 << 16, 100);
    __asm__
    (
        "li x18, %0\n"
        "li x19, %1\n"
        "1:\n"
        "blt x18,x19,1b\n"
        :
        : "i"(a), "i"(b)
        : "x18", "x19"
    );

    // --------------------------------------
    // bge
    // --------------------------------------
    printf("Test BGE to zero offset\n");
    a = 0x7fffffff;
    b = 0xffffffff;
    mm_ram_assert_irq(0x1 << 16, 100);
    __asm__
    (
        "li x18, %0\n"
        "li x19, %1\n"
        "1:\n"
        "bge x18,x19,1b\n"
        :
        : "i"(a), "i"(b)
        : "x18", "x19"
    );

    // --------------------------------------
    // bltu
    // --------------------------------------
    printf("Test BLTU to zero offset\n");
    a = 0x12345678;
    b = 0x12345679;
    mm_ram_assert_irq(0x1 << 16, 100);
    __asm__
    (
        "li x18, %0\n"
        "li x19, %1\n"
        "1:\n"
        "bltu x18,x19,1b\n"
        :
        : "i"(a), "i"(b)
        : "x18", "x19"
    );

    // --------------------------------------
    // bge
    // --------------------------------------
    printf("Test BGEU to zero offset\n");
    a = 0xffffffff;
    b = 0xffffffff;
    mm_ram_assert_irq(0x1 << 16, 100);
    __asm__
    (
        "li x18, %0\n"
        "li x19, %1\n"
        "1:\n"
        "bgeu x18,x19,1b\n"
        :
        : "i"(a), "i"(b)
        : "x18", "x19"
    );

    // --------------------------------------
    // c.beqz
    // --------------------------------------
    printf("Test C.BEQZ to zero offset\n");
    a = 0;
    mm_ram_assert_irq(0x1 << 17, 100);
    __asm__
    (
        "li x15, %0\n"
        "1:\n"
        "c.beqz x15,1b\n"
        :
        : "i"(a)
        : "x15"
    );

    // --------------------------------------
    // c.bnez
    // --------------------------------------
    printf("Test C.BNEZ to zero offset\n");
    a = 0xffffffff;
    mm_ram_assert_irq(0x1 << 17, 100);
    __asm__
    (
        "li x15, %0\n"
        "1:\n"
        "c.bnez x15,1b\n"
        :
        : "i"(a)
        : "x15"
    );
}