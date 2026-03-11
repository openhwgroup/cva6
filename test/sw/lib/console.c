// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

#include <stdint.h>
#include "console.h"

void console_putchar(char character) {
    uintptr_t addr = (uintptr_t)__base_console;
    *(volatile char *)addr = character;
}

void console_puts(char *s, unsigned int n) {
    for (unsigned int i = 0; i < n; ++i)
        console_putchar(s[i]);
}

// Redefine _putchar for printf support
void _putchar(char character) {
    console_putchar(character);
}
