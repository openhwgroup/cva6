// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

#include <stdint.h>
#include "clic.h"

void clic_setup(uint32_t irq_num, int vectored) {
    uint32_t clicint_value = clic_read_clicint(irq_num);
    // Set interrupt as edge-triggered, enable it, and set it as non-privileged
    clicint_value |= (1 << CLICINT_ATTR_TRIG_BIT);               // Edge-triggered
    clicint_value |= (1 << CLICINT_IE_BIT);                      // Enable interrupt
    clicint_value |= (0xaa << CLICINT_CTL_BIT);                  // Set interrupt level and priority
    if (vectored) clicint_value |= (1 << CLICINT_ATTR_SHV_BIT);  // Vectored interrupt
    else          clicint_value &= ~(1 << CLICINT_ATTR_SHV_BIT); // Non-vectored interrupt
    clic_write_clicint(irq_num, clicint_value);
}

void clic_set_pending(uint32_t irq_num) {
    uint32_t clicint_value = clic_read_clicint(irq_num);
    clicint_value |= (1 << CLICINT_IP_BIT); // Set pending bit
    clic_write_clicint(irq_num, clicint_value);
}
void clic_clear_pending(uint32_t irq_num) {
    uint32_t clicint_value = clic_read_clicint(irq_num);
    clicint_value &= ~(1 << CLICINT_IP_BIT); // Clear pending bit
    clic_write_clicint(irq_num, clicint_value);
}
