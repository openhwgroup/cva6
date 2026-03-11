// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

#pragma once

#include <stdint.h>

static inline uint32_t read32(uintptr_t address) {
    return *(uint32_t *)address;
}

static inline void write32(uintptr_t address, uint32_t value) {
    *(uint32_t *)address = value;
}

static inline void set_mtvec(uintptr_t address, int enable_clic) {
    uint64_t value = address & ~0x3; // Ensure address is aligned to 4 bytes
    if (enable_clic) {
        value |= 0x3;
    }
    asm volatile ("csrw mtvec, %0" :: "r"(value));
}

static inline void set_mtvt(uintptr_t address) {
    uint64_t value = address & ~0xFF; // Ensure address is aligned to 256 bytes
    asm volatile ("csrw 0x307, %0" :: "r"(value));
}

// Enables or disables M-mode global interrupts
static inline void set_global_mie(int enable) {
    if (enable)
        asm volatile("csrsi mstatus, 8" ::: "memory");
    else
        asm volatile("csrci mstatus, 8" ::: "memory");
}

static inline void set_mintthresh(uint64_t value) {
    asm volatile ("csrw 0x347, %0" :: "r"(value));
}
