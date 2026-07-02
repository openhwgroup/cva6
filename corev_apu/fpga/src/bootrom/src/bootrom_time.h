// Copyright (c) 2025 Thales Research and Technology
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
/**
 * \file bootrom_time.h
 * \brief Contains a custom udelay function. It is a software wait with a loop that does not uses any hardware timer or any pre-existing timer. As such, the duration is not accurate at all. udelay(5) will not be a 5 microsecond wait. This solution is however good enough for our bootrom as it keeps the code small and still does a decent wait.
 * \author Julien Mallet
*/

#ifndef BOOTROM_TIME_H
#define BOOTROM_TIME_H

#include "bootrom_types.h"

// #define UDELAY(nr_us) for(volatile unsigned int count=0 ; count<50*nr_us ; count++){}

void udelay(u32_t nr_us)
{
	volatile u32_t count = 0;
	for(count = 0 ; count < 1*nr_us; ++count)
	{}
}


#endif