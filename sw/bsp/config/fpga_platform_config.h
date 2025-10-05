// Copyright (c) 2020 Thales.
// 
// Copyright and related rights are licensed under the Apache
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// https://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author:         Sebastien Jacq - sjthales on github.com
//
// Additional contributions by:
//
//
// file Name:      CVA6 FPGA configurtion
// Project Name:   CVA6 softcore
// Language:       C header
//
// Description:    File which defines the FPGA platform, i.e base address for each 
//                 peripheral and others information relating to FPGA platform.
//
// =========================================================================== #
// Revisions  :
// Date        Version  Author       Description
// 2020-10-06  0.1      S.Jacq       Created
// =========================================================================== #

#ifndef __FPGA_PLATFORM_CONFIG_H
#define __FPGA_PLATFORM_CONFIG_H


/***************************************************************************//**
 * Platform frequency
 */

#define FPGA_UART_0_FREQUENCY 40000000


/***************************************************************************//**
 * Peripheral base address
 */
#define FPGA_UART_0_BASE 0x10000000



#endif /* FPGA_PLATFORM_CONFIG */
