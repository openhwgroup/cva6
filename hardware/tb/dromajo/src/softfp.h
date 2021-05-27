/*
 * SoftFP Library
 *
 * Copyright (c) 2016 Fabrice Bellard
 *
 * Licensed under the Apache License, Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * THIS FILE IS BASED ON THE RISCVEMU SOURCE CODE WHICH IS DISTRIBUTED
 * UNDER THE FOLLOWING LICENSE:
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
#ifndef SOFTFP_H
#define SOFTFP_H

#include <inttypes.h>
#include "cutils.h"

typedef enum {
    RM_RNE, /* Round to Nearest, ties to Even */
    RM_RTZ, /* Round towards Zero */
    RM_RDN, /* Round Down */
    RM_RUP, /* Round Up */
    RM_RMM, /* Round to Nearest, ties to Max Magnitude */
} RoundingModeEnum;

#define FFLAG_INVALID_OP  (1 << 4)
#define FFLAG_DIVIDE_ZERO (1 << 3)
#define FFLAG_OVERFLOW    (1 << 2)
#define FFLAG_UNDERFLOW   (1 << 1)
#define FFLAG_INEXACT     (1 << 0)

#define FCLASS_NINF       (1 << 0)
#define FCLASS_NNORMAL    (1 << 1)
#define FCLASS_NSUBNORMAL (1 << 2)
#define FCLASS_NZERO      (1 << 3)
#define FCLASS_PZERO      (1 << 4)
#define FCLASS_PSUBNORMAL (1 << 5)
#define FCLASS_PNORMAL    (1 << 6)
#define FCLASS_PINF       (1 << 7)
#define FCLASS_SNAN       (1 << 8)
#define FCLASS_QNAN       (1 << 9)

typedef uint32_t sfloat32;
typedef uint64_t sfloat64;
#ifdef HAVE_INT128
typedef uint128_t sfloat128;
#endif

/* 32 bit floats */

#define FSIGN_MASK32 (1 << 31)

sfloat32 add_sf32(sfloat32 a, sfloat32 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 sub_sf32(sfloat32 a, sfloat32 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 mul_sf32(sfloat32 a, sfloat32 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 div_sf32(sfloat32 a, sfloat32 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 sqrt_sf32(sfloat32 a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 fma_sf32(sfloat32 a, sfloat32 b, sfloat32 c, RoundingModeEnum rm, uint32_t *pfflags);

sfloat32 min_sf32(sfloat32 a, sfloat32 b, uint32_t *pfflags);
sfloat32 max_sf32(sfloat32 a, sfloat32 b, uint32_t *pfflags);
int eq_quiet_sf32(sfloat32 a, sfloat32 b, uint32_t *pfflags);
int le_sf32(sfloat32 a, sfloat32 b, uint32_t *pfflags);
int lt_sf32(sfloat32 a, sfloat32 b, uint32_t *pfflags);
uint32_t fclass_sf32(sfloat32 a);

sfloat64 cvt_sf32_sf64(sfloat32 a, uint32_t *pfflags);
sfloat32 cvt_sf64_sf32(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
int32_t cvt_sf32_i32(sfloat32 a, RoundingModeEnum rm, uint32_t *pfflags);
uint32_t cvt_sf32_u32(sfloat32 a, RoundingModeEnum rm, uint32_t *pfflags);
int64_t cvt_sf32_i64(sfloat32 a, RoundingModeEnum rm, uint32_t *pfflags);
uint64_t cvt_sf32_u64(sfloat32 a, RoundingModeEnum rm, uint32_t *pfflags);
#ifdef HAVE_INT128
int128_t cvt_sf32_i128(sfloat32 a, RoundingModeEnum rm, uint32_t *pfflags);
uint128_t cvt_sf32_u128(sfloat32 a, RoundingModeEnum rm, uint32_t *pfflags);
#endif
sfloat32 cvt_i32_sf32(int32_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 cvt_u32_sf32(uint32_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 cvt_i64_sf32(int64_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 cvt_u64_sf32(uint64_t a, RoundingModeEnum rm, uint32_t *pfflags);
#ifdef HAVE_INT128
sfloat32 cvt_i128_sf32(int128_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat32 cvt_u128_sf32(uint128_t a, RoundingModeEnum rm, uint32_t *pfflags);
#endif

/* 64 bit floats */

#define FSIGN_MASK64 ((uint64_t)1 << 63)

sfloat64 add_sf64(sfloat64 a, sfloat64 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 sub_sf64(sfloat64 a, sfloat64 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 mul_sf64(sfloat64 a, sfloat64 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 div_sf64(sfloat64 a, sfloat64 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 sqrt_sf64(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 fma_sf64(sfloat64 a, sfloat64 b, sfloat64 c, RoundingModeEnum rm, uint32_t *pfflags);

sfloat64 min_sf64(sfloat64 a, sfloat64 b, uint32_t *pfflags);
sfloat64 max_sf64(sfloat64 a, sfloat64 b, uint32_t *pfflags);
int eq_quiet_sf64(sfloat64 a, sfloat64 b, uint32_t *pfflags);
int le_sf64(sfloat64 a, sfloat64 b, uint32_t *pfflags);
int lt_sf64(sfloat64 a, sfloat64 b, uint32_t *pfflags);
uint32_t fclass_sf64(sfloat64 a);

sfloat64 cvt_sf32_sf64(sfloat32 a, uint32_t *pfflags);
sfloat32 cvt_sf64_sf32(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
int32_t cvt_sf64_i32(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
uint32_t cvt_sf64_u32(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
int64_t cvt_sf64_i64(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
uint64_t cvt_sf64_u64(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
#ifdef HAVE_INT128
int128_t cvt_sf64_i128(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
uint128_t cvt_sf64_u128(sfloat64 a, RoundingModeEnum rm, uint32_t *pfflags);
#endif
sfloat64 cvt_i32_sf64(int32_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 cvt_u32_sf64(uint32_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 cvt_i64_sf64(int64_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 cvt_u64_sf64(uint64_t a, RoundingModeEnum rm, uint32_t *pfflags);
#ifdef HAVE_INT128
sfloat64 cvt_i128_sf64(int128_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat64 cvt_u128_sf64(uint128_t a, RoundingModeEnum rm, uint32_t *pfflags);
#endif

/* 128 bit floats */

#ifdef HAVE_INT128

#define FSIGN_MASK128 ((uint128_t)1 << 127)

sfloat128 add_sf128(sfloat128 a, sfloat128 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 sub_sf128(sfloat128 a, sfloat128 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 mul_sf128(sfloat128 a, sfloat128 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 div_sf128(sfloat128 a, sfloat128 b, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 sqrt_sf128(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 fma_sf128(sfloat128 a, sfloat128 b, sfloat128 c, RoundingModeEnum rm, uint32_t *pfflags);

sfloat128 min_sf128(sfloat128 a, sfloat128 b, uint32_t *pfflags);
sfloat128 max_sf128(sfloat128 a, sfloat128 b, uint32_t *pfflags);
int eq_quiet_sf128(sfloat128 a, sfloat128 b, uint32_t *pfflags);
int le_sf128(sfloat128 a, sfloat128 b, uint32_t *pfflags);
int lt_sf128(sfloat128 a, sfloat128 b, uint32_t *pfflags);
uint32_t fclass_sf128(sfloat128 a);

sfloat128 cvt_sf32_sf128(sfloat32 a, uint32_t *pfflags);
sfloat32 cvt_sf128_sf32(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 cvt_sf64_sf128(sfloat64 a, uint32_t *pfflags);
sfloat64 cvt_sf128_sf64(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);

int32_t cvt_sf128_i32(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);
uint32_t cvt_sf128_u32(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);
int64_t cvt_sf128_i64(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);
uint64_t cvt_sf128_u64(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);
int128_t cvt_sf128_i128(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);
uint128_t cvt_sf128_u128(sfloat128 a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 cvt_i32_sf128(int32_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 cvt_u32_sf128(uint32_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 cvt_i64_sf128(int64_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 cvt_u64_sf128(uint64_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 cvt_i128_sf128(int128_t a, RoundingModeEnum rm, uint32_t *pfflags);
sfloat128 cvt_u128_sf128(uint128_t a, RoundingModeEnum rm, uint32_t *pfflags);

#endif

#endif /* SOFTFP_H */
