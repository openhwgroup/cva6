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

#pragma once

#include "flexfloat.h"

#include <iostream>
#include <sstream>
#include <bitset>


// Collection of statistics

#ifdef FLEXFLOAT_STATS

#include <unordered_map>
#include <utility>

struct OpsStats {
    uint64_t minus;
    uint64_t add;
    uint64_t sub;
    uint64_t mul;
    uint64_t div;
    uint64_t cmp;

    OpsStats(): minus(0), add(0), sub(0), mul(0), div(0), cmp(0) { }
};

struct CastingStats {

    uint64_t total;

    CastingStats(): total(0) { }

};

typedef std::pair<uint_fast8_t, uint_fast8_t> FlexfloatPrecision;

static inline FlexfloatPrecision make_precision(uint_fast8_t a, uint_fast8_t b)
{
    return std::make_pair(a, b);
}

static inline std::pair<FlexfloatPrecision, FlexfloatPrecision> make_precision(uint_fast8_t a1, uint_fast8_t b1, uint_fast8_t a2, uint_fast8_t b2)
{
    return std::make_pair(make_precision(a1, b1), make_precision(a2, b2));
}

static inline FlexfloatPrecision get_type_precision(const int &v)
{
    return std::make_pair((uint_fast8_t) 100, (uint_fast8_t) 132);
}

static inline FlexfloatPrecision get_type_precision(const float &v)
{
    return std::make_pair((uint_fast8_t) 108, (uint_fast8_t) 123);
}

static inline FlexfloatPrecision get_type_precision(const double &v)
{
    return std::make_pair((uint_fast8_t) 111, (uint_fast8_t) 152);
}

struct PrecisionHash {
    std::size_t operator()(FlexfloatPrecision const& p) const
    {
        std::size_t h1 = std::hash<uint_fast8_t>{}(p.first);
        std::size_t h2 = std::hash<uint_fast8_t>{}(p.second);
        return h1 ^ (h2 << 1);
    }
};

struct PrecisionPairHash {
    std::size_t operator()(std::pair<FlexfloatPrecision, FlexfloatPrecision> const& pp) const
    {
        std::size_t h1 = PrecisionHash{}(pp.first);
        std::size_t h2 = PrecisionHash{}(pp.second);
        return h1 ^ (h2 << 1);
    }
};

static std::unordered_map<FlexfloatPrecision, OpsStats, PrecisionHash> ops_stats;
static std::unordered_map<FlexfloatPrecision, OpsStats, PrecisionHash> vops_stats;
static std::unordered_map<std::pair<FlexfloatPrecision, FlexfloatPrecision>, CastingStats, PrecisionPairHash> casting_stats;
static std::unordered_map<std::pair<FlexfloatPrecision, FlexfloatPrecision>, CastingStats, PrecisionPairHash> vcasting_stats;

static bool flexfloat_vectorization;

static bool flexfloat_stats_enabled;

static inline void flexfloat_start_stats() {
    flexfloat_stats_enabled = true;
}

static inline void flexfloat_stop_stats() {
    flexfloat_stats_enabled = false;
}

static inline void flexfloat_clear_stats() {
    ops_stats.clear();
    vops_stats.clear();
    casting_stats.clear();
    vcasting_stats.clear();
}

static inline void flexfloat_print_stats() {
    const int PADDING = 4;

    std::cout << std::endl << "-- OPERATIONS -- " << std::endl;
    for(auto& stat: ops_stats)
    {
        std::cout << "flexfloat<" << int(stat.first.first) << ", " << int(stat.first.second) << ">" << std::endl;
        std::cout << std::string(PADDING, ' ') << "ADD   \t" << stat.second.add << std::endl;
        std::cout << std::string(PADDING, ' ') << "SUB   \t" << stat.second.sub << std::endl;
        std::cout << std::string(PADDING, ' ') << "MUL   \t" << stat.second.mul << std::endl;
        std::cout << std::string(PADDING, ' ') << "DIV   \t" << stat.second.div << std::endl;
        std::cout << std::string(PADDING, ' ') << "MINUS \t" << stat.second.minus << std::endl;
        std::cout << std::string(PADDING, ' ') << "CMP   \t" << stat.second.cmp << std::endl;
    }

    std::cout << std::endl << "-- VECTORIZED OPERATIONS -- " << std::endl;
    for(auto& stat: vops_stats)
    {
        std::cout << "flexfloat<" << int(stat.first.first) << ", " << int(stat.first.second) << ">" << std::endl;
        std::cout << std::string(PADDING, ' ') << "ADD    \t" << stat.second.add << std::endl;
        std::cout << std::string(PADDING, ' ') << "SUB    \t" << stat.second.sub << std::endl;
        std::cout << std::string(PADDING, ' ') << "MUL    \t" << stat.second.mul << std::endl;
        std::cout << std::string(PADDING, ' ') << "DIV    \t" << stat.second.div << std::endl;
        std::cout << std::string(PADDING, ' ') << "MINUS  \t" << stat.second.minus << std::endl;
        std::cout << std::string(PADDING, ' ') << "CMP    \t" << stat.second.cmp << std::endl;
    }

    std::cout << std::endl << "-- CASTS -- " << std::endl;
    for(auto& stat: casting_stats)
    {
      std::cout << "flexfloat<" << int(stat.first.first.first) << ", " << int(stat.first.first.second) << "> -> " ;
      std::cout << "flexfloat<" << int(stat.first.second.first) << ", " << int(stat.first.second.second) << ">  \t ";
      std::cout << stat.second.total << std::endl;
    }

    std::cout << std::endl << "-- VECTORIZED CASTS -- " << std::endl;
    for(auto& stat: vcasting_stats)
    {
      std::cout << "flexfloat<" << int(stat.first.first.first) << ", " << int(stat.first.first.second) << "> -> " ;
      std::cout << "flexfloat<" << int(stat.first.second.first) << ", " << int(stat.first.second.second) << ">  \t ";
      std::cout << stat.second.total << std::endl;
    }
}

#endif // FLEXFLOAT_STATS


/* STREAM MANIPULATORS */

// Get the first unused global index value in the  private storage of std::ios_base
static INLINE int get_manipulator_id() {
    static int id = std::ios_base::xalloc();
    return id;
}

// Set output mode to double format
static INLINE std::ostream& flexfloat_as_double(std::ostream& os) {
    os.iword(get_manipulator_id()) = 0;
    return os;
}

// Set output mode to bits format
static INLINE std::ostream& flexfloat_as_bits(std::ostream& os) {
    os.iword(get_manipulator_id()) = 1;
    return os;
}


/* FLEXFLOAT CLASS */

template <uint_fast8_t exp_bits, uint_fast8_t frac_bits> class flexfloat {
protected:
    flexfloat_t v;

public:

    INLINE fp_t getValue() const {
        return v.value;
    }

    // Empty constructor --> initialize to positive zero.
    INLINE flexfloat ()
    {
        v.value = 0.0;
        v.desc.exp_bits = exp_bits;
        v.desc.frac_bits = frac_bits;
    }

    INLINE flexfloat (const flexfloat &o) {
        v.value = o.getValue();
        v.desc.exp_bits = exp_bits;
        v.desc.frac_bits = frac_bits;
    }

   INLINE flexfloat (flexfloat &&o) noexcept : v(o.v) {  } ;


   INLINE flexfloat& operator = (const flexfloat &o) {
        v.value = o.getValue();
        v.desc.exp_bits = exp_bits;
        v.desc.frac_bits = frac_bits;
        return *this;
    }

    INLINE flexfloat& operator = (const flexfloat &&o) noexcept {
        v = o.v;
        return *this;
    }

    // Constructor from flexfloat types
    template <uint_fast8_t e, uint_fast8_t f> INLINE flexfloat (const flexfloat<e, f> &w) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) {
            if(flexfloat_vectorization) vcasting_stats[make_precision(e, f, exp_bits, frac_bits)].total++;
            else casting_stats[make_precision(e, f, exp_bits, frac_bits)].total++;
        }
#endif
        v.value = w.getValue();
        v.desc.exp_bits = exp_bits;
        v.desc.frac_bits = frac_bits;
        flexfloat_sanitize(&v);
    }

    // Constructor from castable type
    template <typename U> INLINE flexfloat (const U &w)
    {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) {
            FlexfloatPrecision p = get_type_precision(w);
            if(flexfloat_vectorization) vcasting_stats[make_precision(p.first, p.second, exp_bits, frac_bits)].total++;
            else casting_stats[make_precision(p.first, p.second, exp_bits, frac_bits)].total++;
        }
#endif
        v.value = fp_t(w);
        v.desc.exp_bits = exp_bits;
        v.desc.frac_bits = frac_bits;

        flexfloat_sanitize(&v);
    }


    /*------------------------------------------------------------------------
    | OPERATOR OVERLOADS: CASTS
    *------------------------------------------------------------------------*/

    INLINE explicit operator flexfloat_t() const {
        return v;
    }

    INLINE explicit operator float() const {
        return float(*(reinterpret_cast<const fp_t *>(&(v.value))));
    }

    INLINE explicit operator double() const {
        return double(*(reinterpret_cast<const fp_t *>(&(v.value))));
    }

    INLINE explicit operator long double() const {
        return (long double)(*(reinterpret_cast<const fp_t *>(&(v.value))));
    }

    INLINE explicit operator __float128() const {
        return (__float128)(*(reinterpret_cast<const fp_t *>(&(v.value))));
    }

    /*------------------------------------------------------------------------
    | OPERATOR OVERLOADS: Arithmetics
    *------------------------------------------------------------------------*/

    /* UNARY MINUS (-) */
    INLINE flexfloat operator-() const
    {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) {
            if(flexfloat_vectorization) vops_stats[make_precision(exp_bits, frac_bits)].minus++;
            else ops_stats[make_precision(exp_bits, frac_bits)].minus++;
        }
#endif
        return flexfloat(- v.value);
    }

    /* UNARY PLUS (+) */
    INLINE flexfloat operator+() const
    {
        return flexfloat(v.value);
    }

    /* ADD (+) */
    friend INLINE flexfloat operator+(const flexfloat &a, const flexfloat &b)
    {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) {
            if(flexfloat_vectorization) vops_stats[make_precision(exp_bits, frac_bits)].add++;
            else ops_stats[make_precision(exp_bits, frac_bits)].add++;
        }
#endif
        return flexfloat(a.v.value + b.v.value);
    }

     /* SUB (-) */
    friend INLINE flexfloat operator-(const flexfloat &a, const flexfloat &b)
    {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) {
            if(flexfloat_vectorization) vops_stats[make_precision(exp_bits, frac_bits)].sub++;
            else ops_stats[make_precision(exp_bits, frac_bits)].sub++;
        }
#endif
        return flexfloat(a.v.value - b.v.value);
    }

     /* MUL (-) */
    friend INLINE flexfloat operator*(const flexfloat &a, const flexfloat &b)
    {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) {
            if(flexfloat_vectorization) vops_stats[make_precision(exp_bits, frac_bits)].mul++;
            else ops_stats[make_precision(exp_bits, frac_bits)].mul++;
        }
#endif
        return flexfloat(a.v.value * b.v.value);
    }

     /* DIV (/) */
    friend INLINE flexfloat operator/(const flexfloat &a, const flexfloat &b)
    {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) {
            if(flexfloat_vectorization) vops_stats[make_precision(exp_bits, frac_bits)].div++;
            else ops_stats[make_precision(exp_bits, frac_bits)].div++;
        }
#endif
        return flexfloat(a.v.value / b.v.value);
    }

    /*------------------------------------------------------------------------
    | OPERATOR OVERLOADS: Relational operators
    *------------------------------------------------------------------------*/


    /* EQUALITY (==) */
    friend INLINE bool operator==(const flexfloat &a, const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].cmp++;
#endif
        return (a.v.value == b.v.value);
    }

    /* INEQUALITY (!=) */
    friend INLINE bool operator!=(const flexfloat &a, const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].cmp++;
#endif
        return (a.v.value != b.v.value);
    }

    /* GREATER-THAN (>) */
    friend INLINE bool operator>(const flexfloat &a, const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].cmp++;
#endif
        return (a.v.value > b.v.value);
    }

    /* LESS-THAN (<) */
    friend INLINE bool operator<(const flexfloat &a, const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].cmp++;
#endif
        return (a.v.value < b.v.value);
    }

    /* GREATER-THAN-OR-EQUAL-TO (>=) */
    friend INLINE bool operator>=(const flexfloat &a, const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].cmp++;
#endif
        return (a.v.value >= b.v.value);
    }

    /* LESS-THAN-OR-EQUAL-TO (<=) */
    friend INLINE bool operator<=(const flexfloat &a, const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].cmp++;
#endif
        return (a.v.value <= b.v.value);
    }

    /*------------------------------------------------------------------------
    | OPERATOR OVERLOADS: Compound assignment operators (no bitwise ops)
    *------------------------------------------------------------------------*/
    INLINE flexfloat &operator+=(const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].add++;
#endif
        return *this = *this + b;
    }

    INLINE flexfloat &operator-=(const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].sub++;
#endif
        return *this = *this - b;
    }

    INLINE flexfloat &operator*=(const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].mul++;
#endif
        return *this = *this * b;
    }

    INLINE flexfloat &operator/=(const flexfloat &b) {
#ifdef FLEXFLOAT_STATS
        if(flexfloat_stats_enabled) ops_stats[make_precision(exp_bits, frac_bits)].div++;
#endif
        return *this = *this / b;
    }

    /*------------------------------------------------------------------------
    | OPERATOR OVERLOADS: IO streams operators
    *------------------------------------------------------------------------*/
    friend std::ostream& operator<<(std::ostream& os, const flexfloat& obj)
    {
        if(os.iword(get_manipulator_id()) == 0)
        {
            #ifndef FLEXFLOAT_ON_QUAD
            os << fp_t(obj);
            #endif
        }
        else
        {
            int_fast16_t exp = flexfloat_exp(&(obj.v));
            uint_t frac;
            if (exp <= 0) {
                frac = flexfloat_denorm_frac(&(obj.v), exp);
                exp = 0;
            }
            else
                frac = flexfloat_frac(&(obj.v));

            os << flexfloat_sign(&(obj.v)) << "-";
            os << std::bitset<exp_bits>(exp) << "-";
            os << std::bitset<frac_bits>(frac);
        }
        return os;
    }

};


/* Testing support */

template <uint_fast8_t e, uint_fast8_t f>
std::string bitstring(const flexfloat<e, f> &ff) noexcept
{
    std::stringstream buffer;
    buffer << flexfloat_as_bits << ff;
    return buffer.str();
}

template <typename T>
std::bitset<NUM_BITS> bits(const T &ff) noexcept
{
    using bitset = std::bitset<NUM_BITS>;
    fp_t val = fp_t(ff);
    return *reinterpret_cast<bitset*>(&val);
}

INLINE uint_t reinterpret_as_bits(fp_t v) noexcept
{
    return CAST_TO_UINT(v);
}

INLINE fp_t reinterpret_bits_as(uint_t v) noexcept
{
    return CAST_TO_FP(v);
}

INLINE uint64_t reinterpret_as_double_bits(fp_t v) noexcept
{
    double v1 = double(v);
    return (*((uint64_t *)(&(v1))));
}

INLINE fp_t reinterpret_double_bits_as(uint64_t v) noexcept
{
    return fp_t(*((double *)(&(v))));
}