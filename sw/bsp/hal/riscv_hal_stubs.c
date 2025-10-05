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
 * @brief MPFS MSS Interrupt Function stubs.
 *
 */
// Additional contributions by:
//         Sebastien Jacq - sjthales on github.com
//
// Description: The functions below will only be linked with the application 
//              code if the user does not provide an implementation for these 
//              functions. These functions are defined with weak linking so that 
//              they can be overridden by a function with same prototype in the 
//              user's application code.
//
// =========================================================================== //
// Revisions  :
// Date        Version  Author       Description
// 2020-10-06  0.1      S.Jacq       modification of the Test for CVA6 softcore
// =========================================================================== //



#include <unistd.h>


__attribute__((weak))  uint8_t NoInterrupt_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t UART_0_PLIC_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t QSPI_0_PLIC_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t ETH_0_PLIC_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_4_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_5_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_6_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_7_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_8_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_9_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_10_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_11_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_12_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_13_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_14_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_15_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_16_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_17_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_18_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_19_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_20_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_21_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_22_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_23_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_24_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_25_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_26_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_27_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_28_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_29_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_30_IRQHandler(void)
{
    return(0);
}

__attribute__((weak))  uint8_t External_31_IRQHandler(void)
{
    return(0);
}


