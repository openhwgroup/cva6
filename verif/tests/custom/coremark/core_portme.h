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

#include <stddef.h>
#include <stdio.h>
#include "uart.h"

typedef signed short   ee_s16;
typedef unsigned short ee_u16;
typedef signed int     ee_s32;
typedef double         ee_f32;
typedef unsigned char  ee_u8;
typedef unsigned int   ee_u32;
#if (!defined(XLEN) || (XLEN == 64))
typedef unsigned long int ee_u64;
typedef ee_u64         ee_ptr_int;
#else
#if (XLEN == 32)
typedef ee_u32         ee_ptr_int;
#else
#error Define XLEN to 32, 64, or leave it undefined (same as defined to 64).
#endif
#endif
typedef size_t         ee_size_t;

typedef ee_ptr_int CORE_TICKS;

// Use static memory allocation
#define MEM_METHOD MEM_STATIC

typedef struct CORE_PORTABLE_S
{
    ee_u8 portable_id;
} core_portable;

#ifndef MULTITHREAD
#define MULTITHREAD 1  // 1 means single-core
#define USE_PTHREAD 0
#define USE_FORK    0
#define USE_SOCKET  0
#endif

#ifndef COMPILER_VERSION
#ifdef __GNUC__
#define COMPILER_VERSION "GCC"__VERSION__
#else
#define COMPILER_VERSION "Undefined non-gcc compiler used"
#endif
#endif

#ifndef COMPILER_FLAGS
#define COMPILER_FLAGS FLAGS_STR
#endif

#ifndef MEM_LOCATION
#define MEM_LOCATION ""
#endif

#ifndef SC_MEM_LOCATION
#define SC_MEM_LOCATION "UNSPECIFIED(" MEM_LOCATION ") RATIOS:1"
#endif

#ifndef SEED_METHOD
#define SEED_METHOD SEED_VOLATILE
#endif

#ifndef HAS_PRINTF
#define HAS_PRINTF 1
#endif

#define printf(...) do { \
        char text[1024]; \
        sprintf(text, __VA_ARGS__); \
        print_uart(text); \
} while (0)

#define align_mem(x) (void *)(4 + (((ee_ptr_int)(x)-1) & ~3))

#define CORETIMETYPE ee_u32

extern ee_u32 default_num_contexts;

void portable_init(core_portable *p, int *argc, char *argv[]);
void portable_fini(core_portable *p);
