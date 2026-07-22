// Copyright (c) 2025 Thales Research and Technology
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
/**
 * \file bootrom_io.h
 * \brief Contains the functions for reading and writing registers.
 * \author Julien Mallet
*/

#ifndef BOOTROM_IO_H
#define BOOTROM_IO_H

// Generic I/O

#include "bootrom_types.h"
#include <stdio.h>


static inline u8_t readb(volatile u32_t addr)
{
	return *(volatile u8_t *)(addr);
}

static inline u16_t readw(volatile u32_t addr)
{
	return *(volatile u16_t *)(addr);
}

static inline u32_t readl(volatile u32_t addr)
{
	return *(volatile u32_t *)(addr);
}


static inline void writeb(u8_t val, volatile u32_t addr)
{
	*(volatile u8_t *)(addr) = val;
}

static inline void writew(u16_t val, volatile u32_t addr)
{
	*(volatile u16_t *)(addr) = val;
}

static inline void writel(u32_t val, volatile u32_t addr)
{
	*(volatile u32_t *)(addr) = val;
}


#endif