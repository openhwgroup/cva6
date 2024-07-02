// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_IF_SV__
`define __UVMA_INTERRUPT_IF_SV__


/**
 * Encapsulates all signals and clocking of Interrupt interface. Used by
 * monitor and driver.
 */
interface uvma_interrupt_if
   (
   );

   logic [uvma_interrupt_pkg::NUM_IRQ-1:0]       irq;

endinterface : uvma_interrupt_if


`endif // __UVMA_INTERRUPT_IF_SV__
