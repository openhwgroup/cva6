// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

#pragma once

// Sim console base address from linker script
extern char __base_console[];

void console_putchar(char character);
void console_puts(char *s, unsigned int n);
