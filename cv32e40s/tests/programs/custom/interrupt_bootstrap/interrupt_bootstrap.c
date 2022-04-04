#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

#include "interrupt_test.h"

// There is no way to commnicate UVM side information to firmware currently
// so use a fixed value for moving mtvec
// This should be safely away from the code area and yet safely "down" the stack area
#define BOOTSTRAP_MTVEC 0x00000200

volatile uint32_t irq_id                  = 0;
volatile uint32_t irq_id_q[IRQ_NUM];
volatile uint32_t irq_id_q_ptr            = 0;
volatile uint32_t mmcause                 = 0;
volatile uint32_t active_test             = 0;
volatile uint32_t nested_irq              = 0;
volatile uint32_t nested_irq_valid        = 0;
volatile uint32_t in_direct_handler       = 0;

uint32_t IRQ_ID_PRIORITY [IRQ_NUM] = {
    FAST15_IRQ_ID   ,
    FAST14_IRQ_ID   ,
    FAST13_IRQ_ID   ,
    FAST12_IRQ_ID   ,
    FAST11_IRQ_ID   ,
    FAST10_IRQ_ID   ,
    FAST9_IRQ_ID    ,
    FAST8_IRQ_ID    ,
    FAST7_IRQ_ID    ,
    FAST6_IRQ_ID    ,
    FAST5_IRQ_ID    ,
    FAST4_IRQ_ID    ,
    FAST3_IRQ_ID    ,
    FAST2_IRQ_ID    ,
    FAST1_IRQ_ID    ,
    FAST0_IRQ_ID    ,
    EXTERNAL_IRQ_ID ,
    SOFTWARE_IRQ_ID ,
    TIMER_IRQ_ID
};

void delay(int count) {
    for (volatile int d = 0; d < count; d++);
}

void mstatus_mie_enable() {
    int mie_bit = 0x1 << MSTATUS_MIE_BIT;
    __asm__ volatile("csrrs x0, mstatus, %0" : : "r" (mie_bit));
}

void mstatus_mie_disable() {
    int mie_bit = 0x1 << MSTATUS_MIE_BIT;
    __asm__ volatile("csrrc x0, mstatus, %0" : : "r" (mie_bit));
}

void mie_enable_all() {
    uint32_t mie_mask = (uint32_t) -1;
    __asm__ volatile("csrrs x0, mie, %0" : : "r" (mie_mask));
}

void mie_disable_all() {
    uint32_t mie_mask = (uint32_t) -1;
    __asm__ volatile("csrrc x0, mie, %0" : : "r" (mie_mask));
}

void mie_enable(uint32_t irq) {
    // Enable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    __asm__ volatile("csrrs x0, mie, %0" : : "r" (mie_bit));
}

void mie_disable(uint32_t irq) {
    // Disable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    __asm__ volatile("csrrc x0, mie, %0" : : "r" (mie_bit));
}

void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay) {
    *TIMER_REG_ADDR = mask;
    *TIMER_VAL_ADDR = 1 + cycle_delay;
}

uint32_t random_num(uint32_t upper_bound, uint32_t lower_bound) {
    uint32_t random_num = *((volatile int *) CV_VP_RANDOM_NUM_BASE);
    uint32_t num = (random_num  % (upper_bound - lower_bound + 1)) + lower_bound;
    return num;
}

uint32_t random_num32() {
    uint32_t num = *((volatile int *)CV_VP_RANDOM_NUM_BASE);
    return num;
}

extern void __no_irq_handler();

void nested_irq_handler(uint32_t id) {
    // First stack mie, mepc and mstatus
    // Must be done in critical section with MSTATUS.MIE == 0
    volatile uint32_t mie, mepc, mstatus;
    __asm__ volatile("csrr %0, mie" : "=r" (mie));
    __asm__ volatile("csrr %0, mepc" :"=r" (mepc));
    __asm__ volatile("csrr %0, mstatus" : "=r" (mstatus));

    // Re enable interrupts and create window to enable nested irqs
    mstatus_mie_enable();
    for (volatile int i = 0; i < 20; i++);

    // Disable MSTATUS.MIE and restore from critical section
    mstatus_mie_disable();
    __asm__ volatile("csrw mie, %0" : : "r" (mie));
    __asm__ volatile("csrw mepc, %0" : : "r" (mepc));
    __asm__ volatile("csrw mstatus, %0" : : "r" (mstatus));
}

void generic_irq_handler(uint32_t id) {
    __asm__ volatile("csrr %0, mcause": "=r" (mmcause));
    irq_id = id;

    if (active_test == 2 || active_test == 3 || active_test == 4) {
        irq_id_q[irq_id_q_ptr++] = id;
    }
    if (active_test == 3) {
        if (nested_irq_valid) {
            nested_irq_valid = 0;
            mm_ram_assert_irq(0x1 << nested_irq, random_num(10,0));
        }
        nested_irq_handler(id);
    }
}

void m_software_irq_handler(void) { generic_irq_handler(SOFTWARE_IRQ_ID); }
void m_timer_irq_handler(void) { generic_irq_handler(TIMER_IRQ_ID); }
void m_external_irq_handler(void) { generic_irq_handler(EXTERNAL_IRQ_ID); }
void m_fast0_irq_handler(void) { generic_irq_handler(FAST0_IRQ_ID); }
void m_fast1_irq_handler(void) { generic_irq_handler(FAST1_IRQ_ID); }
void m_fast2_irq_handler(void) { generic_irq_handler(FAST2_IRQ_ID); }
void m_fast3_irq_handler(void) { generic_irq_handler(FAST3_IRQ_ID); }
void m_fast4_irq_handler(void) { generic_irq_handler(FAST4_IRQ_ID); }
void m_fast5_irq_handler(void) { generic_irq_handler(FAST5_IRQ_ID); }
void m_fast6_irq_handler(void) { generic_irq_handler(FAST6_IRQ_ID); }
void m_fast7_irq_handler(void) { generic_irq_handler(FAST7_IRQ_ID); }
void m_fast8_irq_handler(void) { generic_irq_handler(FAST8_IRQ_ID); }
void m_fast9_irq_handler(void) { generic_irq_handler(FAST9_IRQ_ID); }
void m_fast10_irq_handler(void) { generic_irq_handler(FAST10_IRQ_ID); }
void m_fast11_irq_handler(void) { generic_irq_handler(FAST11_IRQ_ID); }
void m_fast12_irq_handler(void) { generic_irq_handler(FAST12_IRQ_ID); }
void m_fast13_irq_handler(void) { generic_irq_handler(FAST13_IRQ_ID); }
void m_fast14_irq_handler(void) { generic_irq_handler(FAST14_IRQ_ID); }
void m_fast15_irq_handler(void) { generic_irq_handler(FAST15_IRQ_ID); }

// A Special version of the SW Handler (vector 0) used in the direct mode
__attribute__((interrupt ("machine"))) void u_sw_direct_irq_handler(void)  {
    in_direct_handler = 1;
    __asm__ volatile("csrr %0, mcause" : "=r" (mmcause));
}

int test_mtvec() {
    uint32_t mtvec_act;
    uint32_t mtvec_exp = BOOTSTRAP_MTVEC | 0x1;

    __asm__ volatile("csrr %0, mtvec" : "=r" (mtvec_act));
    if (mtvec_act != mtvec_exp) {
        printf("MTVEC bootstrap failure, exp 0x%08lx, act 0x%08lx\n", mtvec_exp, mtvec_act);
        return 1;
    }
    return EXIT_SUCCESS;
}

int main(int argc, char *argv[]) {
    int retval;

    // Trash the "default" 0 table
    for (int i = 0; i < 32; i++) {
        volatile uint32_t *ptr = (volatile uint32_t *) (0 + i*4);
        *ptr = 0x0;
    }

    // Test that mtvec is correct
    retval = test_mtvec();
    if (retval != EXIT_SUCCESS)
        return retval;

    // Test 1
    retval = test1();
    if (retval != EXIT_SUCCESS)
        return retval;
}

// Test 1 will issue individual interrupts one at a time and ensure that each ISR is entered
int test1() {
    printf("TEST 1 - TRIGGER ALL IRQS IN SEQUENCE:\n");

    active_test = 1;

    if (test1_impl(0) != EXIT_SUCCESS)
        return ERR_CODE_TEST_1;

    return EXIT_SUCCESS;
}

// To share implementation of basic interrupt test with vector relocation tests,
// break out the test 1 implementation here
int test1_impl(int direct_mode) {
    for (uint32_t i = 0; i < 32; i++) {
#ifdef DEBUG_MSG
        printf("Test1 -> Testing interrupt %lu\n", i);
#endif
        for (uint32_t gmie = 0; gmie <= 1; gmie++) {
            for (uint32_t mie = 0; mie <= 1; mie++) {
                uint32_t mip;

                // Set global MIE
                if (gmie) mstatus_mie_enable();
                else mstatus_mie_disable();

                // Set individual mie
                if (mie) mie_enable(i);
                else mie_disable(i);

                in_direct_handler = 0;
                mmcause = 0;
                mm_ram_assert_irq(0x1 << i, 1);

                if (((0x1 << i) & IRQ_MASK) && mie && gmie) {
                    // Interrupt is valid and enabled
                    // wait for the irq to be served
                    while (!mmcause);

                    if ((mmcause & (0x1 << 31)) == 0) {
                        printf("MCAUSE[31] was not set: mmcause = 0x%08lx\n", (uint32_t) mmcause);

                        return ERR_CODE_TEST_1;
                    }
                    if ((mmcause & MCAUSE_IRQ_MASK) != i) {
                        printf("MCAUSE reported wrong irq, exp = %lu, act = 0x%08lx", i, mmcause);

                        return ERR_CODE_TEST_1;
                    }
                } else {
                    // Unimplemented interrupts, or is a masked irq, delay a bit, waiting for any mmcause
                    for (int j = 0; j < 20; j++) {
                        if (mmcause != 0) {
                            printf("MMCAUSE = 0x%08lx when unimplmented interrupt %lu first", mmcause, i);
                            return ERR_CODE_TEST_1;
                        }
                    }
                }

                // Check MIP
                // For unimplemented irqs, this should always be 0
                // For masked irqs, this should always be 0
                // If the IRQ occurred then acking will cause it to clear by here, so do not check
                __asm__ volatile ("csrr %0,mip" : "=r" (mip));
                if (((0x1 << i) & IRQ_MASK) && (!mie || !gmie)) {
                    // Implemented, masked IRQ
                    if (!(mip & (0x1 << i))) {
                        printf("MIP for IRQ[%lu] not set\n", i);
                        return ERR_CODE_TEST_1;
                    }
                } else {
                    // Unimplemented IRQ
                    if (mip & (0x1 << i)) {
                        printf("MIP for unimplemented IRQ[%lu] set\n", i);
                        return ERR_CODE_TEST_1;
                    }
                }

                // Check flag at direct mode handler
                if (((0x1 << i) & IRQ_MASK) && mie && gmie) {
                    if (direct_mode && !in_direct_handler) {
                        printf("In direct mode, the direct sw handler was not entered, irq: %lu\n", i);
                        return ERR_CODE_TEST_1;
                    }
                    if (!direct_mode && in_direct_handler) {
                        printf("In vector mode, the direct sw handler was entered, irq: %lu\n", i);
                        return ERR_CODE_TEST_1;
                    }
                }

                // Clear vp irq
                mm_ram_assert_irq(0, 0);
            }
        }
    }

    return EXIT_SUCCESS;
}

