// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

#pragma once

#define CLICINT_OFFSET 0x1000

#define CLICINT_IP_BIT         0
#define CLICINT_IE_BIT         8
#define CLICINT_ATTR_SHV_BIT  16
#define CLICINT_ATTR_TRIG_BIT 17
#define CLICINT_CTL_BIT       24

#include <stdint.h>
#include <util.h>

// CLIC base address from linker script
extern char __base_clic[];

static inline uint32_t clic_read_clicint(uint32_t irq_num) {
    uintptr_t CLIC_BASE = (uintptr_t)__base_clic;
    return read32(CLIC_BASE + CLICINT_OFFSET + irq_num * 4);
}

static inline void clic_write_clicint(uint32_t irq_num, uint32_t value) {
    uintptr_t CLIC_BASE = (uintptr_t)__base_clic;
    write32(CLIC_BASE + CLICINT_OFFSET + irq_num * 4, value);
}

void clic_setup(uint32_t irq_num, int vectored);
void clic_set_pending(uint32_t irq_num);
void clic_clear_pending(uint32_t irq_num);
