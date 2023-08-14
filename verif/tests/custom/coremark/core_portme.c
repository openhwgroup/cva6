/*
Copyright 2018 Embedded Microprocessor Benchmark Consortium (EEMBC)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Original Author: Shay Gal-on
*/

// Copyright 2020 OpenHW Group
// Copyright 2020 Silicon Labs, Inc.
// Copyright 2022 Thales DIS Design Services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0

#include "coremark.h"

ee_u32 default_num_contexts = 1;

static CORETIMETYPE start_time_val, stop_time_val;

#if VALIDATION_RUN
volatile ee_s32 seed1_volatile = 0x3415;
volatile ee_s32 seed2_volatile = 0x3415;
volatile ee_s32 seed3_volatile = 0x66;
#endif
#if PERFORMANCE_RUN
volatile ee_s32 seed1_volatile = 0x0;
volatile ee_s32 seed2_volatile = 0x0;
volatile ee_s32 seed3_volatile = 0x66;
#endif
#if PROFILE_RUN
volatile ee_s32 seed1_volatile = 0x8;
volatile ee_s32 seed2_volatile = 0x8;
volatile ee_s32 seed3_volatile = 0x8;
#endif
volatile ee_s32 seed4_volatile = ITERATIONS;
volatile ee_s32 seed5_volatile = 0;

void
portable_init(core_portable *p, int *argc, char *argv[])
{
    // Don't need to do anything here atm.
    (void)p;
    (void)argc;
    (void)argv;
}

void
portable_fini(core_portable *p)
{
    // Don't need to do anything here atm.
    (void)p;
}

// Provided by custom syscalls.c
extern void setStats(int enable);
extern ee_ptr_int getStats(int counterid);

void
start_time(void)
{
    setStats(1);
}

void
stop_time(void)
{
    setStats(0);
}

CORE_TICKS
get_time(void)
{
    ee_ptr_int cycles_lo = getStats(0);  // mcycle
    // We may need to access mcycleh as well (FORNOW getStats(2)).

    return cycles_lo;
}

secs_ret
time_in_secs(CORE_TICKS ticks)
{
    return ((secs_ret) ticks)/1000000;  // Pretend we use 1 MHz clock.
}
