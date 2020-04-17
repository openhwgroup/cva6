/*
   Copyright 2018 - The OPRECOMP Project Consortium, Alma Mater Studiorum
   Università di Bologna. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

/* C++ */
#ifdef __cplusplus
extern "C" {
#endif

#ifndef flexfloat_h
#define flexfloat_h 1

#include "flexfloat_config.h"

#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>

// If not specified with FLEXFLOAT_NO_ROUNDING flag, rounding is active
#ifndef FLEXFLOAT_NO_ROUNDING
#define FLEXFLOAT_ROUNDING
#endif

// Backend value precision
#if !defined(FLEXFLOAT_ON_SINGLE) && !defined(FLEXFLOAT_ON_DOUBLE) && !defined(FLEXFLOAT_ON_QUAD)
#error "A backend type must be specified (FLEXFLOAT_ON_SINGLE, FLEXFLOAT_ON_DOUBLE or FLEXFLOAT_ON_QUAD)"
#endif

#ifdef FLEXFLOAT_ON_SINGLE
#define UINT_C UINT32_C
#define MASK_FRAC (UINT32_C(0x007FFFFF))
#define MASK_FRAC_MSB (UINT32_C(0x00800000))
#define MASK_FRAC_EXCEPT_MSB (UINT32_C(0x003FFFFF))
#define SMALLEST_NORM_POS (0x00800000)
#define SMALLEST_NORM_NEG (0x80800000)
#define INF_EXP (0xFF)
#define BIAS (127)
#define NUM_BITS (32)
#define NUM_BITS_EXP (8)
#define NUM_BITS_FRAC (23)
typedef int32_t int_t;
typedef uint32_t uint_t;
typedef float fp_t;
#define PRINTF_FORMAT "%.7f"
#endif /* FLEXFLOAT_ON_SINGLE */

#ifdef FLEXFLOAT_ON_DOUBLE
#define UINT_C UINT64_C
#define MASK_FRAC (UINT64_C(0x000FFFFFFFFFFFFF))
#define MASK_FRAC_MSB (UINT64_C(0x0010000000000000))
#define MASK_FRAC_EXCEPT_MSB (UINT64_C(0x0007FFFFFFFFFFFF))
#define SMALLEST_NORM_POS (0x0010000000000000)
#define SMALLEST_NORM_NEG (0x8010000000000000)
#define INF_EXP (0x7FF)
#define BIAS (1023)
#define NUM_BITS (64)
#define NUM_BITS_EXP (11)
#define NUM_BITS_FRAC (52)
typedef int64_t int_t;
typedef uint64_t uint_t;
typedef double fp_t;
#define PRINTF_FORMAT "%.18f"
#endif /* FLEXFLOAT_ON_DOUBLE */

#ifdef FLEXFLOAT_ON_QUAD
#include <quadmath.h>
typedef __int128 int128_t;
typedef unsigned __int128 uint128_t;
#define UINT_C(c) ((uint128_t)c)
static uint64_t mask_frac_value[2] = {0xFFFFFFFFFFFFFFFF, 0x0000FFFFFFFFFFFF};
#define MASK_FRAC (*((uint128_t *)(&(mask_frac_value))))
static uint64_t mask_frac_msb_value[2] = {0x0000000000000000, 0x0001000000000000};
#define MASK_FRAC_MSB (*((uint128_t *)(&(mask_frac_msb_value))))
static uint64_t mask_frac_except_msb_value[2] = {0xFFFFFFFFFFFFFFFF, 0x00007FFFFFFFFFFF};
#define MASK_FRAC_EXCEPT_MSB (*((uint128_t *)(&(mask_frac_except_msb_value))))
static uint64_t smallest_norm_pos_value[2] = {0x0000000000000000, 0x0001000000000000};
#define SMALLEST_NORM_POS (*((uint128_t *)(&(smallest_norm_pos_value))))
static uint64_t smallest_norm_neg_value[2] = {0x0000000000000000, 0x8001000000000000};
#define SMALLEST_NORM_NEG (*((uint128_t *)(&(smallest_norm_neg_value))))
#define INF_EXP (0x7FFF)
#define BIAS (16383)
#define NUM_BITS (128)
#define NUM_BITS_EXP (15)
#define NUM_BITS_FRAC (112)
typedef int128_t int_t;
typedef uint128_t uint_t;
typedef __float128 fp_t;
#define PRINTF_FORMAT "%.38Lf"
#endif /* FLEXFLOAT_ON_QUAD */


// Helper macros

#define SIGN( a ) ((bool) ((uint_t) (a)>>(NUM_BITS-1)))
#define EXPONENT( a ) ((int_fast16_t) ((uint_t) (a)>>NUM_BITS_FRAC) & INF_EXP)
#define PACK( sign, exp, sig ) ((uint_t) (((uint_t) (sign)<<(NUM_BITS-1)) + ((uint_t) (exp)<<NUM_BITS_FRAC) + (sig)))

#define CAST_TO_INT(d) (*((int_t *)(&(d))))
#define CAST_TO_UINT(d) (*((uint_t *)(&(d))))
#define CAST_TO_FP(d) (*((fp_t *)(&(d))))

#ifndef INLINE
#define INLINE inline
#endif


// Types

struct _flexfloat_t;
typedef struct _flexfloat_t flexfloat_t;
typedef void (*ff_function_p)(flexfloat_t *, void *);

typedef struct _flexfloat_desc_t {
    uint8_t exp_bits;
    uint8_t frac_bits;
} flexfloat_desc_t;

struct _flexfloat_t {
    fp_t value;
#ifdef FLEXFLOAT_TRACKING
    fp_t exact_value;
    ff_function_p tracking_fn;
    void * tracking_arg;
#endif
    flexfloat_desc_t desc;
};


// Helper functions

static inline int_fast16_t flexfloat_inf_exp(const flexfloat_desc_t desc)
{
    return (int_fast16_t) (((int_fast16_t)1 << desc.exp_bits) - 1);
}

static inline int_fast16_t flexfloat_bias(const flexfloat_desc_t desc)
{
    return (int_fast16_t) (((int_fast16_t)1 << (desc.exp_bits - 1)) - 1);
}

static inline bool flexfloat_sign(const flexfloat_t *a)
{
    return (CAST_TO_INT(a->value)) >> (NUM_BITS-1);
}

int_fast16_t flexfloat_exp(const flexfloat_t *a);
uint_t flexfloat_frac(const flexfloat_t *a);
uint_t flexfloat_denorm_frac(const flexfloat_t *a, int_fast16_t exp);
uint_t flexfloat_pack(flexfloat_desc_t desc, bool sign, int_fast16_t exp, uint_t frac);
void flexfloat_sanitize(flexfloat_t *a);


// Bit-level access

uint_t flexfloat_pack_bits(flexfloat_desc_t desc, uint_t bits);
void flexfloat_set_bits(flexfloat_t *a, uint_t bits);
uint_t flexfloat_get_bits(flexfloat_t *a);


// Constructors

void ff_init(flexfloat_t *obj, flexfloat_desc_t desc);
void ff_init_float(flexfloat_t *obj, float value, flexfloat_desc_t desc);
void ff_init_double(flexfloat_t *obj, double value, flexfloat_desc_t desc);
void ff_init_longdouble(flexfloat_t *obj, long double value, flexfloat_desc_t desc);
void ff_init_float128(flexfloat_t *obj, __float128 value, flexfloat_desc_t desc);
void ff_init_int(flexfloat_t *obj, int value, flexfloat_desc_t desc);
void ff_init_long(flexfloat_t *obj, long value, flexfloat_desc_t desc);
void ff_cast(flexfloat_t *obj, const flexfloat_t *source, flexfloat_desc_t desc);

// Casts

float ff_get_float(const flexfloat_t *obj);
double ff_get_double(const flexfloat_t *obj);
long double ff_get_longdouble(const flexfloat_t *obj);
__float128 ff_get_float128(const flexfloat_t *obj);


// Artihmetic operators

void ff_inverse(flexfloat_t *dest, const flexfloat_t *a);
void ff_add(flexfloat_t *dest, const flexfloat_t *a, const flexfloat_t *b);
void ff_sub(flexfloat_t *dest, const flexfloat_t *a, const flexfloat_t *b);
void ff_mul(flexfloat_t *dest, const flexfloat_t *a, const flexfloat_t *b);
void ff_div(flexfloat_t *dest, const flexfloat_t *a, const flexfloat_t *b);
void ff_acc(flexfloat_t *dest, const flexfloat_t *a);


// Relational operators

bool ff_eq(const flexfloat_t *a, const flexfloat_t *b);
bool ff_neq(const flexfloat_t *a, const flexfloat_t *b);
bool ff_le(const flexfloat_t *a, const flexfloat_t *b);
bool ff_lt(const flexfloat_t *a, const flexfloat_t *b);
bool ff_ge(const flexfloat_t *a, const flexfloat_t *b);
bool ff_gt(const flexfloat_t *a, const flexfloat_t *b);


// Collection of statistics

#ifdef FLEXFLOAT_STATS

#ifndef FLEXFLOAT_STATS_MAX_TYPES
#define FLEXFLOAT_STATS_MAX_TYPES 128
#endif

typedef struct {
    uint32_t key;
    void    *value;
} HashSlot;

extern bool StatsEnabled;
extern HashSlot   op_stats[FLEXFLOAT_STATS_MAX_TYPES];
extern HashSlot cast_stats[FLEXFLOAT_STATS_MAX_TYPES*FLEXFLOAT_STATS_MAX_TYPES];

typedef struct {
    uint64_t minus;
    uint64_t add;
    uint64_t sub;
    uint64_t mul;
    uint64_t div;
    uint64_t cmp;
} OpStats;

typedef struct {
    uint64_t total;
} CastStats;

typedef struct __attribute__((__packed__))  {
    uint8_t exp_bits1;
    uint8_t frac_bits1;
    uint8_t exp_bits2;
    uint8_t frac_bits2;
} KeyStruct;

static inline uint32_t precision_hash (const flexfloat_desc_t desc)
{
    return desc.exp_bits ^ (desc.frac_bits << 8);
}

static inline uint32_t precision_hash2 (const flexfloat_desc_t desc1, const flexfloat_desc_t desc2)
{
    return desc1.exp_bits ^ (desc1.frac_bits << 8) ^ (desc2.exp_bits << 16) ^ (desc2.frac_bits << 24);
}

OpStats * getOpStats(const flexfloat_desc_t desc);
CastStats * getCastStats(const flexfloat_desc_t desc1, const flexfloat_desc_t desc2);

void ff_start_stats();
void ff_stop_stats();
void ff_clear_stats();
void ff_print_stats();

#endif /* FLEXFLOAT_STATS */


// Advanced tracking support

#ifdef FLEXFLOAT_TRACKING

static inline fp_t ff_track_get_exact (const flexfloat_t *a) {
    return a->exact_value;
}

static inline fp_t ff_track_get_error (const flexfloat_t *a) {
    return a->value - a->exact_value;
}

static inline void ff_track_callback (flexfloat_t *a, ff_function_p fn, void *arg ) {
    a->tracking_fn = fn;
    a->tracking_arg = arg;
}

#endif /* FLEXFLOAT_TRACKING */

#endif

/* C++ */
#ifdef __cplusplus
}
#endif
