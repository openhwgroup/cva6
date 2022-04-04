#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "interrupt_test.h"

volatile uint32_t irq_id                  = 0;
volatile uint32_t irq_id_q[IRQ_NUM];
volatile uint32_t irq_id_q_ptr            = 0;
volatile uint32_t mmcause                 = 0;
volatile uint32_t active_test             = 0;
volatile uint32_t nested_irq              = 0;
volatile uint32_t nested_irq_valid        = 0;
volatile uint32_t in_direct_handler       = 0;
volatile uint32_t event;
volatile uint32_t num_taken_interrupts;
volatile uint32_t num_counted_interrupts;

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

// FIXME: Create VP register for a timer on reliable time-base (i.e. cpu clock)
// FIXME: Add to common infrastructure
void delay(int count) {
    for (volatile int d = 0; d < count; d++);
}

void mstatus_mie_enable() {
    int mie_bit = 0x1 << MSTATUS_MIE_BIT;
    asm volatile("csrrs x0, mstatus, %0" : : "r" (mie_bit));
}

void mstatus_mie_disable() {
    int mie_bit = 0x1 << MSTATUS_MIE_BIT;
    asm volatile("csrrc x0, mstatus, %0" : : "r" (mie_bit));
}

void mie_enable_all() {
    uint32_t mie_mask = (uint32_t) -1;
    asm volatile("csrrs x0, mie, %0" : : "r" (mie_mask));
}

void mie_disable_all() {
    uint32_t mie_mask = (uint32_t) -1;
    asm volatile("csrrc x0, mie, %0" : : "r" (mie_mask));
}

void mie_enable(uint32_t irq) {
    // Enable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    asm volatile("csrrs x0, mie, %0" : : "r" (mie_bit));
}

void mie_disable(uint32_t irq) {
    // Disable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    asm volatile("csrrc x0, mie, %0" : : "r" (mie_bit));
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
    uint32_t num = *((volatile int *) CV_VP_RANDOM_NUM_BASE);
    return num;
}

extern void __no_irq_handler();

void nested_irq_handler(uint32_t id) {
    // First stack mie, mepc and mstatus
    // Must be done in critical section with MSTATUS.MIE == 0
    volatile uint32_t mie, mepc, mstatus;
    asm volatile("csrr %0, mie" : "=r" (mie));
    asm volatile("csrr %0, mepc" :"=r" (mepc));
    asm volatile("csrr %0, mstatus" : "=r" (mstatus));

    // Re enable interrupts and create window to enable nested irqs
    mstatus_mie_enable();
    for (volatile int i = 0; i < 20; i++);

    // Disable MSTATUS.MIE and restore from critical section
    mstatus_mie_disable();
    asm volatile("csrw mie, %0" : : "r" (mie));
    asm volatile("csrw mepc, %0" : : "r" (mepc));
    asm volatile("csrw mstatus, %0" : : "r" (mstatus));
}

void generic_irq_handler(uint32_t id) {
    asm volatile("csrr %0, mcause": "=r" (mmcause));
    asm volatile("csrr %0, 0xB03" : "=r" (num_counted_interrupts));
    irq_id = id;

    // Increment if interrupt
    if (mmcause >> 31) {
      num_taken_interrupts++;
    }

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
    asm volatile("csrr %0, mcause" : "=r" (mmcause));
    if (mmcause >> 31) {
      num_taken_interrupts++;
    }
}

    asm (
        ".global alt_vector_table\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_vector_table:\n"
	    "j u_sw_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j m_software_irq_handler\n"
	    "j __no_irq_handler\n"
        "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j m_timer_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j m_external_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j m_fast0_irq_handler\n"
	    "j m_fast1_irq_handler\n"
	    "j m_fast2_irq_handler\n"
	    "j m_fast3_irq_handler\n"
	    "j m_fast4_irq_handler\n"
	    "j m_fast5_irq_handler\n"
	    "j m_fast6_irq_handler\n"
	    "j m_fast7_irq_handler\n"
	    "j m_fast8_irq_handler\n"
	    "j m_fast9_irq_handler\n"
	    "j m_fast10_irq_handler\n"
	    "j m_fast11_irq_handler\n"
	    "j m_fast12_irq_handler\n"
	    "j m_fast13_irq_handler\n"
	    "j m_fast14_irq_handler\n"
	    "j m_fast15_irq_handler\n"
    );

    asm (
        ".global alt_direct_vector_table\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_direct_vector_table:\n"
	    "j u_sw_direct_irq_handler\n"
    );

    asm (
        ".global alt_direct_ecall_table\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_direct_ecall_table:\n"
        "wfi\n"
	    "j u_sw_irq_handler\n"
    );

int main(int argc, char *argv[]) {
    int retval;

    num_counted_interrupts = 0;
    num_taken_interrupts   = 0;

    // Enable interrupt performance counter (mhpmcounter3)
    event = EVENT_INTR_TAKEN;
    __asm__ volatile ("csrw 0x323, %0 " :: "r"(event));
    __asm__ volatile ("csrwi 0xB03, 0x0");
    __asm__ volatile ("csrwi 0x320, 0x0");

  // Test 1
  retval = test1();
  if (retval != EXIT_SUCCESS) {
    return retval;
  }

    // Test 2
    retval = test2();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    // Test 3
    retval = test3();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    // Test 4
    retval = test4();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    // Test 5
    retval = test5();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    // Test 6
    retval = test6();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    // Repeat test1 (restore vector mode)
    retval = test7();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    // Try to write mcause (for coverage)
    retval = test8();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    // Test 9
    retval = test9();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    // Clear MIE for final WFI
    mie_disable_all();

    // Check that the interrupt taken counter
    if (num_counted_interrupts != num_taken_interrupts) {
      printf("mhpmcounter3 (number of events taken) does not match actual interrupts taken: %0d != %0d\n", (int)num_counted_interrupts, (int)num_taken_interrupts);
      return ERR_CODE_INTR_CNT;
    }

    return EXIT_SUCCESS;
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

    //-------------------------------------------------------------------------------------------------------------------------------------------
    //-------------------------------------------------------------------------------------------------------------------------------------------

// Test 2 will issue all interrupts at once and check that all interrupt are serviced in priority order
int test2() {
    printf("TEST 2 - TRIGGER ALL IRQS AT ONCE:\n");
    active_test = 2;

    // Clear VP irq
    mm_ram_assert_irq(0, 0);

    // Enable all interrupts (MIE and MSTATUS.MIE)
    uint32_t mie = (uint32_t) -1;
    asm volatile("csrw mie, %0" : : "r" (mie));
    mstatus_mie_enable();
    irq_id_q_ptr = 0;

    // Fire all IRQs and give time for them to be handled
    mm_ram_assert_irq((uint32_t) -1, 0);

    delay(100);

    for (int i = 0; i < IRQ_NUM; i++) {
        // The irq_id_q should now contain interrupt IDs in the same order as IRQ_ID_PRIORITY
        if (IRQ_ID_PRIORITY[i] != irq_id_q[i]) {
            printf("priority mismatch, index %d, exp %lu, act %lu\n",
                    i, IRQ_ID_PRIORITY[i], irq_id_q[i]);
            return ERR_CODE_TEST_2;
        }
    }

    return EXIT_SUCCESS;
}

    //-------------------------------------------------------------------------------------------------------------------------------------------
    //-------------------------------------------------------------------------------------------------------------------------------------------

// Test 3 will create nested interrupts
int test3() {
    printf("TEST 3 - NESTED INTERRUPTS:\n");

    // Test 3 is a nested interrupt test
    active_test = 3;

    // Enable all interrupts
    mm_ram_assert_irq(0, 0);
    mie_enable_all();
    mstatus_mie_enable();

    // Set 2 interrupts
    for (uint32_t loop = 0; loop < 50; loop++) {
        uint32_t irq[2];

        // Pick 2 random interrupts
        irq[0] = IRQ_ID_PRIORITY[random_num(IRQ_NUM-1, 0)];
        irq[1] = IRQ_ID_PRIORITY[random_num(IRQ_NUM-1, 0)];

        irq_id_q_ptr = 0;
        nested_irq = irq[1];
        nested_irq_valid = 1;

#ifdef DEBUG_MSG
        printf("TEST3: Test nested irqs %lu and %lu\n", irq[0], irq[1]);
#endif

        mm_ram_assert_irq(0x1 << irq[0], 0);

        delay(50);

        if (irq_id_q[0] != irq[0]) {
            printf("TEST3, first interrupt exp %lu act %lu\n", irq[0], irq_id_q[0]);
            return ERR_CODE_TEST_3;
        }
        if (irq_id_q[1] != irq[1]) {
            printf("TEST3, second interrupt exp %lu act %lu\n", irq[1], irq_id_q[1]);
            return ERR_CODE_TEST_3;
        }
    }

    return EXIT_SUCCESS;
}

    //-------------------------------------------------------------------------------------------------------------------------------------------
    //-------------------------------------------------------------------------------------------------------------------------------------------

// Test 4 will test WFI mode
// Ensures that only MIE-enabled interrupts wake WFI
// Tests that WFI works regardless of MSTATUS.MIE
// Tests that IRQ handler is not entered after WFI unless MSTATUS.MIE is set
int test4() {
    printf("TEST 4 - WFI\n");

    // Test 4 is a WFI test
    active_test = 4;

    // Iterate through multiple loops
    for (int irq = 0; irq < 32; irq++) {
        if (!(((0x1 << irq) & IRQ_MASK)))
            continue;

        for (uint32_t gmie = 0; gmie <= 1; gmie++) {
            uint32_t rand_irq;

            // Clear MIE and all pending irqs
            mie_disable_all();
            mm_ram_assert_irq(0, 0);

            // Select a wakeup interrupt and enable only it
            mie_enable(irq);

            // Prep the IRQ ID Q to be empty, we need to detect if any interrupts (or none) taken
            irq_id_q[0] = -1;
            irq_id_q_ptr = 0;

            // Set the global MSTATUS.MIE
            // Note that WFI should ignore this (but subsequent ISR will not be taken if MSTATUS.MIE == 0)
            if (gmie)
                mstatus_mie_enable();
            else
                mstatus_mie_disable();

            // Assert random batch of irqs (w/o selected irq)
            rand_irq = random_num32() & ~(0x1 << irq);
            mm_ram_assert_irq(rand_irq, 0);

            delay(2);

            // Random assert "enabled" irq
            mm_ram_assert_irq(rand_irq | (0x1 << irq), (random_num32() & 0x3f) + 32);
            asm volatile("wfi");


            if (gmie) {
                // Expected an interrupt taken
                if (irq_id_q[0] != irq) {
                    printf("After WFI, expected to hit an interrupt, but irq_id_q is empty\n");
                    return ERR_CODE_TEST_4;
                }
            } else {
                // Expected no interrupt taken
                if (irq_id_q[0] != -1) {
                    printf("After WFI with MSTATUS.MIE == 0, interrupt was taken: %lu\n", irq_id_q[0]);
                    return ERR_CODE_TEST_4;
                }
            }
        }
    }
    return EXIT_SUCCESS;
}

// Test 5 will repeat the basic interrupt test in test 1
// But with a relocated vector table via mtvec CSR
int test5() {
    volatile uint32_t save_mtvec;
    int retval;

    printf("TEST 5 - TRIGGER ALL IRQS IN SEQUENCE (RELOCATED MTVEC):\n");

    active_test = 5;

    asm volatile("csrr %0, mtvec" : "=r" (save_mtvec));
    asm volatile("csrw mtvec, %0" : : "r" ((uint32_t) alt_vector_table | (save_mtvec & 0x3)));

    retval = test1_impl(0);
    asm volatile("csrw mtvec, %0" : : "r" (save_mtvec));
    if (retval != EXIT_SUCCESS) {
        return ERR_CODE_TEST_5;
    }

    return EXIT_SUCCESS;
}

// Test 6 will repeat the basic interrupt test in test 1
// But with a relocated vector table via mtvec CSR and DIRECT vector mode
int test6() {
    volatile uint32_t save_mtvec;
    int retval;

    printf("TEST 6 - TRIGGER ALL IRQS IN SEQUENCE (DIRECT-MODE MTVEC):\n");

    active_test = 6;

    asm volatile("csrr %0, mtvec" : "=r" (save_mtvec));
    asm volatile("csrw mtvec, %0" : : "r" ((uint32_t) alt_direct_vector_table)); // Leave mode at 0

    retval = test1_impl(1);
    asm volatile("csrw mtvec, %0" : : "r" (save_mtvec));
    if (retval != EXIT_SUCCESS) {
        return ERR_CODE_TEST_6;
    }

    return EXIT_SUCCESS;
}

// Test 7 is a direct repeat of test 1 in vectored mode
int test7() {
    printf("TEST 7 - TRIGGER ALL IRQS IN SEQUENCE: (REPEAT VECTOR MODE)\n");

    active_test = 7;

    if (test1_impl(0) != EXIT_SUCCESS)
        return ERR_CODE_TEST_7;

    return EXIT_SUCCESS;
}

int test8() {
    volatile uint32_t mcausew;
    volatile uint32_t mcauser;

    // MCAUSE is writable, this simple check tests this and also fufills code coverage
    printf("TEST 8 - READ/WRITE TO MCAUSE\n");

    mcausew = 0x0;
    __asm__ volatile("csrw mcause, %0" : : "r"(mcausew));
    __asm__ volatile("csrr %0, mcause" : "=r"(mcauser));
    if (mcauser != 0) {
        printf("MCAUSE write-read error, exp: 0x0, act: 0x%lx\n", mcauser);
        return EXIT_FAILURE;
    }

    mcausew = 0x1f;
    __asm__ volatile("csrw mcause, %0" : : "r"(mcausew));
    __asm__ volatile("csrr %0, mcause" : "=r"(mcauser));
    if (mcauser != mcausew) {
        printf("MCAUSE write-read error, exp: 0x1f, act: 0x%lx\n", mcauser);
        return EXIT_FAILURE;
    }

    mcausew = 0x0;
    __asm__ volatile("csrw mcause, %0" : : "r"(mcausew));
    __asm__ volatile("csrr %0, mcause" : "=r"(mcauser));
    if (mcauser != 0) {
        printf("MCAUSE write-read error, exp: 0x0, act: 0x%lx\n", mcauser);
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}

int test9() {
    volatile uint32_t save_mtvec;
    printf("TEST 9 - ECALL-WFI Coverage Test\n");

    active_test = 9;

    asm volatile("csrr %0, mtvec" : "=r" (save_mtvec));
    asm volatile("csrw mtvec, %0" : : "r" ((uint32_t) alt_direct_ecall_table)); // Leave mode at 0

    mm_ram_assert_irq(0, 0);

    // Iterate through multiple loops
    for (int irq = 0; irq < 32; irq++) {
        if (!(((0x1 << irq) & IRQ_MASK)))
            continue;

        for (uint32_t gmie = 0; gmie <= 0; gmie++) {
            uint32_t rand_irq;

            // Clear MIE and all pending irqs
            mie_disable_all();

            // Select a wakeup interrupt and enable only it
            mie_enable(irq);

            // Prep the IRQ ID Q to be empty, we need to detect if any interrupts (or none) taken
            irq_id_q[0] = -1;
            irq_id_q_ptr = 0;

            // Set the global MSTATUS.MIE
            // Note that WFI should ignore this (but subsequent ISR will not be taken if MSTATUS.MIE == 0)
            if (gmie)
                mstatus_mie_enable();
            else
                mstatus_mie_disable();

            // Assert random batch of irqs (w/o selected irq)
            rand_irq = random_num32() & ~(0x1 << irq);
            mm_ram_assert_irq(rand_irq, 0);

            delay(2);

            // Random assert "enabled" irq
            mm_ram_assert_irq(rand_irq | (0x1 << irq), (random_num32() & 0x3f) + 64);
            asm volatile("ecall");

            if (gmie) {
                // Expected an interrupt taken
                if (irq_id_q[0] != irq) {
                    printf("After WFI, expected to hit an interrupt, but irq_id_q is empty\n");
                    return ERR_CODE_TEST_4;
                }
            } else {
                // Expected no interrupt taken
                if (irq_id_q[0] != -1) {
                    printf("After WFI with MSTATUS.MIE == 0, interrupt was taken: %lu\n", irq_id_q[0]);
                    return ERR_CODE_TEST_4;
                }
            }
        }
    }

    asm volatile("csrw mtvec, %0" : : "r" (save_mtvec));

    return EXIT_SUCCESS;
}
