// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#ifndef __INTERRUPT_TEST_H__
#define __INTERRUPT_TEST_H__

#include <stdint.h>
#include <stdbool.h>
#include "corev_uvmt.h"
// Enable debug messages, note that this will change test timing
//#define DEBUG_MSG

#define ERR_CODE_TEST_1      1
#define ERR_CODE_TEST_2      2
#define ERR_CODE_TEST_3      3
#define ERR_CODE_TEST_4      4
#define ERR_CODE_TEST_5      5
#define ERR_CODE_TEST_6      6
#define ERR_CODE_TEST_7      7

#define ERR_CODE_INTR_CNT    8

#define TIMER_REG_ADDR       ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE))
#define TIMER_VAL_ADDR       ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE + 4))

#define MSTATUS_MIE_BIT 3

#define MCAUSE_IRQ_MASK 0x1f

#define EVENT_INTR_TAKEN (1 << 6)

#define IRQ_NUM 19
#define IRQ_MASK 0xFFFF0888

#define SOFTWARE_IRQ_ID  3
#define TIMER_IRQ_ID     7
#define EXTERNAL_IRQ_ID  11
#define FAST0_IRQ_ID     16
#define FAST1_IRQ_ID     17
#define FAST2_IRQ_ID     18
#define FAST3_IRQ_ID     19
#define FAST4_IRQ_ID     20
#define FAST5_IRQ_ID     21
#define FAST6_IRQ_ID     22
#define FAST7_IRQ_ID     23
#define FAST8_IRQ_ID     24
#define FAST9_IRQ_ID     25
#define FAST10_IRQ_ID    26
#define FAST11_IRQ_ID    27
#define FAST12_IRQ_ID    28
#define FAST13_IRQ_ID    29
#define FAST14_IRQ_ID    30
#define FAST15_IRQ_ID    31

void delay(int count);
void mstatus_mie_enable();
void mstatus_mie_disable();
void mie_enable_all();
void mie_disable_all();
void mie_enable(uint32_t irq);
void mie_disable(uint32_t irq);
void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay);
uint32_t random_num(uint32_t upper_bound, uint32_t lower_bound);
uint32_t random_num32();
extern void __no_irq_handler();
void nested_irq_handler(uint32_t id);
void generic_irq_handler(uint32_t id);

__attribute__((interrupt ("machine"))) void m_software_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_timer_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_external_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast0_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast1_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast2_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast3_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast4_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast5_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast6_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast7_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast8_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast9_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast10_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast11_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast12_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast13_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast14_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast15_irq_handler(void);

// A Special version of the SW Handler (vector 0) used in the direct mode
__attribute__((interrupt ("machine"))) void u_sw_direct_irq_handler(void);

extern void alt_vector_table();
extern void alt_direct_vector_table();
extern void alt_direct_ecall_table();

// Function prototypes for individual tests
int test1();
int test2();
int test3();
int test4();
int test5();
int test6();
int test7();
int test8();
int test9();

// Test1 (all irqs in sequence) used in multiple tests so break out implementation
int test1_impl(int direct_mode);

#endif

