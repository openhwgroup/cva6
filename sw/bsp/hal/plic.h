/*******************************************************************************
 * Copyright (c) 2020 Thales.
 * Copyright 2019-2020 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 *
 * @author Microchip-FPGA Embedded Systems Solutions
 *
 * Definitions and functions associated with PLIC interrupts.
 */
// Additional contributions by:
//         Sebastien Jacq - sjthales on github.com
//
// Description: Definitions and functions associated with PLIC interrupts
//              for the CVA6 platform
//
// =========================================================================== //
// Revisions  :
// Date        Version  Author       Description
// 2020-10-06  0.1      S.Jacq       modification of the Test for CVA6 softcore
// =========================================================================== //

#ifndef MSS_PLIC_H
#define MSS_PLIC_H

#include <stdint.h>
#include "encoding.h"

#include "hal_assert.h"

/*
 *Return value from External IRQ handler. This will be used to disable the
 *Return External interrupt.
 */
#define EXT_IRQ_KEEP_ENABLED                                0U
#define EXT_IRQ_DISABLE                                     1U



/***************************************************************************//**
 * PLIC source Interrupt numbers:
 */

typedef enum
{
    NoInterrupt_IRQHandler         = 0,    
    UART_0_PLIC_IRQHandler         = 1,
    QSPI_0_PLIC_IRQHandler         = 2,
    ETH_0_PLIC_IRQHandler          = 3, 
    External_4_IRQHandler  = 4,
    External_5_IRQHandler  = 5,
    External_6_IRQHandler  = 6,
    External_7_IRQHandler  = 7,
    External_8_IRQHandler  = 8,
    External_9_IRQHandler  = 9,
    External_10_IRQHandler = 10,
    External_11_IRQHandler = 11,
    External_12_IRQHandler = 12,
    External_13_IRQHandler = 13,
    External_14_IRQHandler = 14,
    External_15_IRQHandler = 15,
    External_16_IRQHandler = 16,
    External_17_IRQHandler = 17,
    External_18_IRQHandler = 18,
    External_19_IRQHandler = 19,
    External_20_IRQHandler = 20,
    External_21_IRQHandler = 21,
    External_22_IRQHandler = 22,
    External_23_IRQHandler = 23,
    External_24_IRQHandler = 24,
    External_25_IRQHandler = 25,
    External_26_IRQHandler = 26,
    External_27_IRQHandler = 27,
    External_28_IRQHandler = 28,
    External_29_IRQHandler = 29,
    External_30_IRQHandler = 30
} PLIC_IRQn_Type;


#define MAX_PLIC_INT External_30_IRQHandler

typedef struct
{
    volatile uint32_t PRIORITY_THRESHOLD;
    volatile uint32_t CLAIM_COMPLETE;
    volatile uint32_t reserved[(0x1000/4)-2];
} IRQ_Target_Type;

typedef struct
{
    volatile uint32_t ENABLES[31U];
} Target_Enables_Type;


#define PLIC_SET_UP_REGISTERS 2U
#define PLIC_NUM_SOURCES      30U     
#define PLIC_NUM_PRIORITIES   7U
#define NUM_CLAIM_REGS        2U



typedef struct
{
    
    volatile uint32_t RESERVED0;
    /*-------------------- Source Priority --------------------*/
    volatile uint32_t SOURCE_PRIORITY[PLIC_NUM_SOURCES];
    volatile uint32_t RESERVED1[(0x1000/4) - (PLIC_NUM_SOURCES + 1)];

    /*-------------------- Pending array --------------------*/
    volatile const uint32_t PENDING_ARRAY[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED2[(0x1000/4) - PLIC_SET_UP_REGISTERS];

    /*-------------------- Target enables --------------------*/
    //volatile Target_Enables_Type TARGET_ENABLES[PLIC_SET_UP_REGISTERS];
    //volatile uint32_t RESERVED3[(0x200000-0x2000) - PLIC_SET_UP_REGISTERS];
    
    /*-----------------Target Mode Enables--------------------*/
    volatile uint32_t HART0_MMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED3a[(0x80/4) - PLIC_SET_UP_REGISTERS];

    volatile uint32_t HART0_SMODE_ENA[PLIC_SET_UP_REGISTERS];
    volatile uint32_t RESERVED3[(0x80/4) - PLIC_SET_UP_REGISTERS];

    volatile uint32_t RESERVED4[(0x200000-0x2000)/4 - PLIC_SET_UP_REGISTERS];

    /*--- Target Priority threshold and claim/complete---------*/
    IRQ_Target_Type TARGET[NUM_CLAIM_REGS];


    
} PLIC_Type;




#define TARGET_OFFSET_HART0_M 0U
#define TARGET_OFFSET_HART0_S 1U

/***************************************************************************//**
 * PLIC: Platform Level Interrupt Controller
 */
#define PLIC_BASE_ADDR 0x0C000000UL

#define PLIC    ((PLIC_Type *)PLIC_BASE_ADDR)

/*-------------------------------------------------------------------------*//**
 * The function PLIC_init() initializes the PLIC controller and enables the
 * global external interrupt bit.
 */

/*-----------------Hart Mode Enables--------------------*/

static inline void PLIC_init(void)
{
    uint32_t inc;
    uint64_t hart_id  = read_csr(mhartid);

    /* Disable all interrupts for the current hart. */
    for(inc = 0UL; inc < PLIC_SET_UP_REGISTERS; inc++)
    {
        PLIC->HART0_MMODE_ENA[inc] = 0U;
        PLIC->HART0_SMODE_ENA[inc] = 0U;
    }

    PLIC->TARGET[TARGET_OFFSET_HART0_M].PRIORITY_THRESHOLD  = 0U;
    /* Disable supervisor level */
    PLIC->TARGET[TARGET_OFFSET_HART0_S].PRIORITY_THRESHOLD  = 7U;
    
    /* Enable machine external interrupts. */
    set_csr(mie, MIP_MEIP);
}


/***************************************************************************//**
 * The function PLIC_EnableIRQ() enables the external interrupt for the
 * interrupt number indicated by the parameter IRQn.
 */
static inline void PLIC_EnableIRQ(PLIC_IRQn_Type IRQn)
{
    uint64_t hart_id  = read_csr(mhartid);

    uint32_t current;

    switch(hart_id)
    {
        case 0:
            current  = PLIC->HART0_MMODE_ENA[IRQn / 32U];
            current |= (uint32_t)1 << (IRQn % 32U);
            PLIC->HART0_MMODE_ENA[IRQn / 32U]  = current;
            break;
        default:
            break;
    }
}

/***************************************************************************//**
 * The function PLIC_DisableIRQ() disables the external interrupt for the
 * interrupt number indicated by the parameter IRQn.
 * NOTE:
 *     This function can be used to disable the external interrupt from outside
 *     external interrupt handler function.
 *     This function MUST NOT be used from within the External Interrupt
 *     handler.
 *     If you wish to disable the external interrupt while the interrupt handler
 *     for that external interrupt is executing then you must use the return
 *     value EXT_IRQ_DISABLE to return from the extern interrupt handler.
 */
static inline void PLIC_DisableIRQ(PLIC_IRQn_Type IRQn)
{
    uint32_t current;
    uint64_t hart_id  = read_csr(mhartid);

    switch(hart_id)
    {
        case 0:
            current = PLIC->HART0_MMODE_ENA[IRQn / 32U];
            current &= ~((uint32_t)1 << (IRQn % 32U));
            PLIC->HART0_MMODE_ENA[IRQn / 32U] = current;
            break;
            default:
            break;
    }
}

/***************************************************************************//**
 * The function PLIC_SetPriority() sets the priority for the external interrupt
 * for the interrupt number indicated by the parameter IRQn.
 */
static inline void PLIC_SetPriority(PLIC_IRQn_Type IRQn, uint32_t priority)
{
    if((IRQn > NoInterrupt_IRQHandler) && (IRQn < PLIC_NUM_SOURCES))
    {
        PLIC->SOURCE_PRIORITY[IRQn-1] = priority;
    }
}

/***************************************************************************//**
 * The function PLIC_GetPriority() returns the priority for the external
 * interrupt for the interrupt number indicated by the parameter IRQn.
 */
static inline uint32_t PLIC_GetPriority(PLIC_IRQn_Type IRQn)
{
    uint32_t ret_val = 0U;

    if((IRQn > NoInterrupt_IRQHandler) && (IRQn < PLIC_NUM_SOURCES))
    {
        ret_val = PLIC->SOURCE_PRIORITY[IRQn-1];
    }

    return(ret_val);
}


/*static inline uint32_t PLIC_pending(PLIC_IRQn_Type IRQn)
{
    return (PLIC->PENDING_ARRAY[IRQn/32U] & (0x01U<<(IRQn%32U)));
}*/

/***************************************************************************//**
 * The function PLIC_ClaimIRQ() claims the interrupt from the PLIC controller.
 */
static inline uint32_t PLIC_ClaimIRQ(void)
{
    unsigned long hart_id = read_csr(mhartid);

    return PLIC->TARGET[hart_id].CLAIM_COMPLETE;
}

/***************************************************************************//**
 * The function PLIC_CompleteIRQ() indicates to the PLIC controller the
 * interrupt is processed and claim is complete.
 */
static inline void PLIC_CompleteIRQ(uint32_t source)
{
    unsigned long hart_id = read_csr(mhartid);

    PLIC->TARGET[hart_id].CLAIM_COMPLETE = source;
}

/***************************************************************************//**
 *
 * The function PLIC_SetPriority_Threshold() sets the threshold for a particular
 * hart. The default threshold on reset is 0.
 * The PFSoC Core Complex supports setting of an interrupt priority threshold
 * via the threshold register. The threshold is a WARL field, where the PFSoC
 * Core Complex supports a maximum threshold of 7.
 * The PFSoC Core Complex will mask all PLIC interrupts of a priority less than
 * or equal to threshold. For example, a threshold value of zero permits all
 * interrupts with non-zero priority, whereas a value of 7 masks all
 * interrupts.
 */
static inline void PLIC_SetPriority_Threshold(uint32_t threshold)
{
    uint64_t hart_id  = read_csr(mhartid);
    //const unsigned long lookup[5U] = {0U, 1U, 3U, 5U, 7U};

    //ASSERT(threshold <= 7);

    PLIC->TARGET[hart_id].PRIORITY_THRESHOLD  = threshold;
}

/***************************************************************************//**
 *  PLIC_ClearPendingIRQ(void)
 *  This is only called by the startup hart and only once
 *  Clears any pending interrupts as PLIC can be in unknown state on startup
 */
static inline void PLIC_ClearPendingIRQ(void)
{
    volatile uint32_t int_num  = PLIC_ClaimIRQ();
    volatile int32_t wait_possible_int;

    while ( int_num != NoInterrupt_IRQHandler)
    {
        uint8_t disable = EXT_IRQ_KEEP_ENABLED;

        PLIC_CompleteIRQ(int_num);
        wait_possible_int = 0xFU;
        while (wait_possible_int)
        {
            wait_possible_int--;
        }
        int_num  = PLIC_ClaimIRQ(); /* obtain interrupt, auto clears  */
    }
}

/***************************************************************************//**
 * This function is only called from one hart on startup
 */
static inline void PLIC_init_on_reset(void)
{
    uint32_t inc;

    /* default all priorities so effectively disabled */
    for(inc = 0U; inc < PLIC_NUM_SOURCES; ++inc)
    {
        /* priority must be greater than threshold to be enabled, so setting to
         * 7 disables */
        PLIC->SOURCE_PRIORITY[inc]  = 0U;
    }

    for(inc = 0U; inc < NUM_CLAIM_REGS; ++inc)
    {
        PLIC->TARGET[inc].PRIORITY_THRESHOLD  = 7U;
    }

    /* and clear all the enables */
    for(inc = 0UL; inc < PLIC_SET_UP_REGISTERS; inc++)
    {
        PLIC->HART0_MMODE_ENA[inc] = 0U;
        PLIC->HART0_SMODE_ENA[inc] = 0U;
    }

    /* clear any pending interrupts- in case already there */
    PLIC_ClearPendingIRQ();
}


#endif  /* MSS_PLIC_H */

