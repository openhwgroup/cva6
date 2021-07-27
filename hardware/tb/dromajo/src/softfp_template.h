/*
 * SoftFP Library
 *
 * Copyright (c) 2016 Fabrice Bellard
 * Copyright (C) 2018,2019, Esperanto Technologies Inc.
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
#if F_SIZE == 32
#define F_UINT uint32_t
#define F_ULONG uint64_t
#define MANT_SIZE 23
#define EXP_SIZE 8
#elif F_SIZE == 64
#define F_UHALF uint32_t
#define F_UINT uint64_t
#ifdef HAVE_INT128
#define F_ULONG uint128_t
#endif
#define MANT_SIZE 52
#define EXP_SIZE 11
#elif F_SIZE == 128
#define F_UHALF uint64_t
#define F_UINT uint128_t
#define MANT_SIZE 112
#define EXP_SIZE 15
#else
#error unsupported F_SIZE
#endif

#define EXP_MASK ((1 << EXP_SIZE) - 1)
#define MANT_MASK (((F_UINT)1 << MANT_SIZE) - 1)
#define SIGN_MASK ((F_UINT)1 << (F_SIZE - 1))
#define IMANT_SIZE (F_SIZE - 2) /* internal mantissa size */
#define RND_SIZE (IMANT_SIZE - MANT_SIZE)
#define QNAN_MASK ((F_UINT)1 << (MANT_SIZE - 1))

/* quiet NaN */
#define F_QNAN glue(F_QNAN, F_SIZE)
#define clz glue(clz, F_SIZE)
#define pack_sf glue(pack_sf, F_SIZE)
#define unpack_sf glue(unpack_sf, F_SIZE)
#define rshift_rnd glue(rshift_rnd, F_SIZE)
#define round_pack_sf glue(roundpack_sf, F_SIZE)
#define normalize_sf glue(normalize_sf, F_SIZE)
#define normalize2_sf glue(normalize2_sf, F_SIZE)
#define issignan_sf glue(issignan_sf, F_SIZE)
#define isnan_sf glue(isnan_sf, F_SIZE)
#define add_sf glue(add_sf, F_SIZE)
#define mul_sf glue(mul_sf, F_SIZE)
#define fma_sf glue(fma_sf, F_SIZE)
#define div_sf glue(div_sf, F_SIZE)
#define sqrt_sf glue(sqrt_sf, F_SIZE)
#define normalize_subnormal_sf glue(normalize_subnormal_sf, F_SIZE)
#define divrem_u glue(divrem_u, F_SIZE)
#define sqrtrem_u glue(sqrtrem_u, F_SIZE)
#define mul_u glue(mul_u, F_SIZE)
#define cvt_sf32_sf glue(cvt_sf32_sf, F_SIZE)
#define cvt_sf64_sf glue(cvt_sf64_sf, F_SIZE)

const F_UINT F_QNAN = (((F_UINT)EXP_MASK << MANT_SIZE) | ((F_UINT)1 << (MANT_SIZE - 1)));

static inline F_UINT pack_sf(uint32_t a_sign, uint32_t a_exp, F_UINT a_mant)
{
    return ((F_UINT)a_sign << (F_SIZE - 1)) |
        ((F_UINT)a_exp << MANT_SIZE) |
        (a_mant & MANT_MASK);
}

static inline F_UINT unpack_sf(uint32_t *pa_sign, int32_t *pa_exp,
                               F_UINT a)
{
    *pa_sign = a >> (F_SIZE - 1);
    *pa_exp = (a >> MANT_SIZE) & EXP_MASK;
    return a & MANT_MASK;
}

static F_UINT rshift_rnd(F_UINT a, int d)
{
    F_UINT mask;
    if (d != 0) {
        if (d >= F_SIZE) {
            a = (a != 0);
        } else {
            mask = ((F_UINT)1 << d) - 1;
            a = (a >> d) | ((a & mask) != 0);
        }
    }
    return a;
}

/* a_mant is considered to have its MSB at F_SIZE - 2 bits */
static F_UINT round_pack_sf(uint32_t a_sign, int a_exp, F_UINT a_mant,
                            RoundingModeEnum rm, uint32_t *pfflags)
{
    int diff;
    uint32_t addend, rnd_bits;

    switch (rm) {
    case RM_RNE:
    case RM_RMM:
        addend = (1 << (RND_SIZE - 1));
        break;
    case RM_RTZ:
        addend = 0;
        break;
    default:
    case RM_RDN:
    case RM_RUP:
        //        printf("s=%d rm=%d m=%x\n", a_sign, rm, a_mant);
        if (a_sign ^ (rm & 1))
            addend = (1 << RND_SIZE) - 1;
        else
            addend = 0;
        break;
    }

    /* potentially subnormal */
    if (a_exp <= 0) {
        BOOL is_subnormal;
        /* Note: we set the underflow flag if the rounded result
           is subnormal and inexact */
        is_subnormal = (a_exp < 0 ||
                        (a_mant + addend) < ((F_UINT)1 << (F_SIZE - 1)));
        diff = 1 - a_exp;
        a_mant = rshift_rnd(a_mant, diff);
        rnd_bits = a_mant & ((1 << RND_SIZE ) - 1);
        if (is_subnormal && rnd_bits != 0) {
            *pfflags |= FFLAG_UNDERFLOW;
        }
        a_exp = 1;
    } else {
        rnd_bits = a_mant & ((1 << RND_SIZE ) - 1);
    }
    if (rnd_bits != 0)
        *pfflags |= FFLAG_INEXACT;
    a_mant = (a_mant + addend) >> RND_SIZE;
    /* half way: select even result */
    if (rm == RM_RNE && rnd_bits == (1 << (RND_SIZE - 1)))
        a_mant &= ~1;
    /* Note the rounding adds at least 1, so this is the maximum
       value */
    a_exp += a_mant >> (MANT_SIZE + 1);
    if (a_mant <= MANT_MASK) {
        /* denormalized or zero */
        a_exp = 0;
    } else if (a_exp >= EXP_MASK) {
        /* overflow */
        if (addend == 0) {
            a_exp = EXP_MASK - 1;
            a_mant = MANT_MASK;
        } else {
            /* infinity */
            a_exp = EXP_MASK;
            a_mant = 0;
        }
        *pfflags |= FFLAG_OVERFLOW | FFLAG_INEXACT;
    }
    return pack_sf(a_sign, a_exp, a_mant);
}

/* a_mant is considered to have at most F_SIZE - 1 bits */
static F_UINT normalize_sf(uint32_t a_sign, int a_exp, F_UINT a_mant,
                           RoundingModeEnum rm, uint32_t *pfflags)
{
    int shift;
    shift = clz(a_mant) - (F_SIZE - 1 - IMANT_SIZE);
    assert(shift >= 0);
    a_exp -= shift;
    a_mant <<= shift;
    return round_pack_sf(a_sign, a_exp, a_mant, rm, pfflags);
}

/* same as normalize_sf() but with a double word mantissa. a_mant1 is
   considered to have at most F_SIZE - 1 bits */
static F_UINT normalize2_sf(uint32_t a_sign, int a_exp, F_UINT a_mant1, F_UINT a_mant0,
                            RoundingModeEnum rm, uint32_t *pfflags)
{
    int l, shift;
    if (a_mant1 == 0) {
        l = F_SIZE + clz(a_mant0);
    } else {
        l = clz(a_mant1);
    }
    shift = l - (F_SIZE - 1 - IMANT_SIZE);
    assert(shift >= 0);
    a_exp -= shift;
    if (shift == 0) {
        a_mant1 |= (a_mant0 != 0);
    } else if (shift < F_SIZE) {
        a_mant1 = (a_mant1 << shift) | (a_mant0 >> (F_SIZE - shift));
        a_mant0 <<= shift;
        a_mant1 |= (a_mant0 != 0);
    } else {
        a_mant1 = a_mant0 << (shift - F_SIZE);
    }
    return round_pack_sf(a_sign, a_exp, a_mant1, rm, pfflags);
}

BOOL issignan_sf(F_UINT a)
{
    uint32_t a_exp1;
    F_UINT a_mant;
    a_exp1 = (a >> (MANT_SIZE - 1)) & ((1 << (EXP_SIZE + 1)) - 1);
    a_mant = a & MANT_MASK;
    return (a_exp1 == (2 * EXP_MASK) && a_mant != 0);
}

BOOL isnan_sf(F_UINT a)
{
    uint32_t a_exp;
    F_UINT a_mant;
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    return (a_exp == EXP_MASK && a_mant != 0);
}


F_UINT add_sf(F_UINT a, F_UINT b, RoundingModeEnum rm,
              uint32_t *pfflags)
{
    uint32_t a_sign, b_sign, a_exp, b_exp;
    F_UINT tmp, a_mant, b_mant;

    /* swap so that  abs(a) >= abs(b) */
    if ((a & ~SIGN_MASK) < (b & ~SIGN_MASK)) {
        tmp = a;
        a = b;
        b = tmp;
    }
    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    b_exp = (b >> MANT_SIZE) & EXP_MASK;
    a_mant = (a & MANT_MASK) << 3;
    b_mant = (b & MANT_MASK) << 3;
    if (unlikely(a_exp == EXP_MASK)) {
        if (a_mant != 0) {
            /* NaN result */
            if (!(a_mant & (QNAN_MASK << 3)) || issignan_sf(b))
                *pfflags |= FFLAG_INVALID_OP;
            return F_QNAN;
        } else if (b_exp == EXP_MASK && a_sign != b_sign) {
            *pfflags |= FFLAG_INVALID_OP;
            return F_QNAN;
        } else {
            /* infinity */
            return a;
        }
    }
    if (a_exp == 0) {
        a_exp = 1;
    } else {
        a_mant |= (F_UINT)1 << (MANT_SIZE + 3);
    }
    if (b_exp == 0) {
        b_exp = 1;
    } else {
        b_mant |= (F_UINT)1 << (MANT_SIZE + 3);
    }
    b_mant = rshift_rnd(b_mant, a_exp - b_exp);
    if (a_sign == b_sign) {
        /* same signs : add the absolute values  */
        a_mant += b_mant;
    } else {
        /* different signs : subtract the absolute values  */
        a_mant -= b_mant;
        if (a_mant == 0) {
            /* zero result : the sign needs a specific handling */
            a_sign = (rm == RM_RDN);
        }
    }
    a_exp += (RND_SIZE - 3);
    return normalize_sf(a_sign, a_exp, a_mant, rm, pfflags);
}

F_UINT glue(sub_sf, F_SIZE)(F_UINT a, F_UINT b, RoundingModeEnum rm,
                            uint32_t *pfflags)
{
    return add_sf(a, b ^ SIGN_MASK, rm, pfflags);
}

static inline F_UINT normalize_subnormal_sf(int32_t *pa_exp, F_UINT a_mant)
{
    int shift;
    shift = MANT_SIZE - ((F_SIZE - 1 - clz(a_mant)));
    *pa_exp = 1 - shift;
    return a_mant << shift;
}

#ifdef F_ULONG

static F_UINT mul_u(F_UINT *plow, F_UINT a, F_UINT b)
{
    F_ULONG r;
    r = (F_ULONG)a * (F_ULONG)b;
    *plow = r;
    return r >> F_SIZE;
}

#else

#define FH_SIZE (F_SIZE / 2)

static F_UINT mul_u(F_UINT *plow, F_UINT a, F_UINT b)
{
    F_UHALF a0, a1, b0, b1, r0, r1, r2, r3;
    F_UINT r00, r01, r10, r11, c;
    a0 = a;
    a1 = a >> FH_SIZE;
    b0 = b;
    b1 = b >> FH_SIZE;

    r00 = (F_UINT)a0 * (F_UINT)b0;
    r01 = (F_UINT)a0 * (F_UINT)b1;
    r10 = (F_UINT)a1 * (F_UINT)b0;
    r11 = (F_UINT)a1 * (F_UINT)b1;

    r0 = r00;
    c = (r00 >> FH_SIZE) + (F_UHALF)r01 + (F_UHALF)r10;
    r1 = c;
    c = (c >> FH_SIZE) + (r01 >> FH_SIZE) + (r10 >> FH_SIZE) + (F_UHALF)r11;
    r2 = c;
    r3 = (c >> FH_SIZE) + (r11 >> FH_SIZE);

    *plow = ((F_UINT)r1 << FH_SIZE) | r0;
    return ((F_UINT)r3 << FH_SIZE) | r2;
}

#undef FH_SIZE

#endif

F_UINT mul_sf(F_UINT a, F_UINT b, RoundingModeEnum rm,
              uint32_t *pfflags)
{
    uint32_t a_sign, b_sign, r_sign;
    int32_t a_exp, b_exp, r_exp;
    F_UINT a_mant, b_mant, r_mant, r_mant_low;

    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);
    r_sign = a_sign ^ b_sign;
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    b_exp = (b >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    b_mant = b & MANT_MASK;
    if (a_exp == EXP_MASK || b_exp == EXP_MASK) {
        if (isnan_sf(a) || isnan_sf(b)) {
            if (issignan_sf(a) || issignan_sf(b)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        } else {
            /* infinity */
            if ((a_exp == EXP_MASK && (b_exp == 0 && b_mant == 0)) ||
                (b_exp == EXP_MASK && (a_exp == 0 && a_mant == 0))) {
                *pfflags |= FFLAG_INVALID_OP;
                return F_QNAN;
            } else {
                return pack_sf(r_sign, EXP_MASK, 0);
            }
        }
    }
    if (a_exp == 0) {
        if (a_mant == 0)
            return pack_sf(r_sign, 0, 0); /* zero */
        a_mant = normalize_subnormal_sf(&a_exp, a_mant);
    } else {
        a_mant |= (F_UINT)1 << MANT_SIZE;
    }
    if (b_exp == 0) {
        if (b_mant == 0)
            return pack_sf(r_sign, 0, 0); /* zero */
        b_mant = normalize_subnormal_sf(&b_exp, b_mant);
    } else {
        b_mant |= (F_UINT)1 << MANT_SIZE;
    }
    r_exp = a_exp + b_exp - (1 << (EXP_SIZE - 1)) + 2;

    r_mant = mul_u(&r_mant_low, a_mant << RND_SIZE, b_mant << (RND_SIZE + 1));
    r_mant |= (r_mant_low != 0);
    return normalize_sf(r_sign, r_exp, r_mant, rm, pfflags);
}

/* fused multiply and add */
F_UINT fma_sf(F_UINT a, F_UINT b, F_UINT c, RoundingModeEnum rm,
              uint32_t *pfflags)
{
    uint32_t a_sign, b_sign, c_sign, r_sign;
    int32_t a_exp, b_exp, c_exp, r_exp, shift;
    F_UINT a_mant, b_mant, c_mant, r_mant1, r_mant0, c_mant1, c_mant0, mask;

    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);
    c_sign = c >> (F_SIZE - 1);
    r_sign = a_sign ^ b_sign;
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    b_exp = (b >> MANT_SIZE) & EXP_MASK;
    c_exp = (c >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    b_mant = b & MANT_MASK;
    c_mant = c & MANT_MASK;
    if (a_exp == EXP_MASK || b_exp == EXP_MASK || c_exp == EXP_MASK) {
        /* IEEE 754-2008 spec, section 7.2 part c:
         *
         * "fusedMultiplyAdd: fusedMultiplyAdd(0, ∞, c) or
         * fusedMultiplyAdd(∞, 0, c) unless c is a quiet NaN; if c is
         * a quiet NaN then it is implementation defined whether the
         * invalid operation exception is signaled"
         *
         * We want to match Spike here.  Spike use John Hauser's
         * softfloat which ignored c.
         */
        if (a_exp == 0 && a_mant == 0 && b_exp == EXP_MASK && b_mant == 0 ||
            b_exp == 0 && b_mant == 0 && a_exp == EXP_MASK && a_mant == 0) {
            *pfflags |= FFLAG_INVALID_OP;
            return F_QNAN;
        }

        if (isnan_sf(a) || isnan_sf(b) || isnan_sf(c)) {
            if (issignan_sf(a) || issignan_sf(b) || issignan_sf(c)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        } else {
            /* infinities */
            if ((a_exp == EXP_MASK && (b_exp == 0 && b_mant == 0)) ||
                (b_exp == EXP_MASK && (a_exp == 0 && a_mant == 0)) ||
                ((a_exp == EXP_MASK || b_exp == EXP_MASK) &&
                 (c_exp == EXP_MASK && r_sign != c_sign))) {
                *pfflags |= FFLAG_INVALID_OP;
                return F_QNAN;
            } else if (c_exp == EXP_MASK) {
                return pack_sf(c_sign, EXP_MASK, 0);
            } else {
                return pack_sf(r_sign, EXP_MASK, 0);
            }
        }
    }
    if (a_exp == 0) {
        if (a_mant == 0)
            goto mul_zero;
        a_mant = normalize_subnormal_sf(&a_exp, a_mant);
    } else {
        a_mant |= (F_UINT)1 << MANT_SIZE;
    }
    if (b_exp == 0) {
        if (b_mant == 0) {
        mul_zero:
            if (c_exp == 0 && c_mant == 0) {
                if (c_sign != r_sign)
                    r_sign = (rm == RM_RDN);
                return pack_sf(r_sign, 0, 0);
            } else {
                return c;
            }
        }
        b_mant = normalize_subnormal_sf(&b_exp, b_mant);
    } else {
        b_mant |= (F_UINT)1 << MANT_SIZE;
    }
    /* multiply */
    r_exp = a_exp + b_exp - (1 << (EXP_SIZE - 1)) + 3;

    r_mant1 = mul_u(&r_mant0, a_mant << RND_SIZE, b_mant << RND_SIZE);
    /* normalize to F_SIZE - 3 */
    if (r_mant1 < ((F_UINT)1 << (F_SIZE - 3))) {
        r_mant1 = (r_mant1 << 1) | (r_mant0 >> (F_SIZE - 1));
        r_mant0 <<= 1;
        r_exp--;
    }

    /* add */
    if (c_exp == 0) {
        if (c_mant == 0) {
            /* add zero */
            r_mant1 |= (r_mant0 != 0);
            return normalize_sf(r_sign, r_exp, r_mant1, rm, pfflags);
        }
        c_mant = normalize_subnormal_sf(&c_exp, c_mant);
    } else {
        c_mant |= (F_UINT)1 << MANT_SIZE;
    }
    c_exp++;
    c_mant1 = c_mant << (RND_SIZE - 1);
    c_mant0 = 0;

    //    printf("r_s=%d r_exp=%d r_mant=%08x %08x\n", r_sign, r_exp, (uint32_t)r_mant1, (uint32_t)r_mant0);
    //    printf("c_s=%d c_exp=%d c_mant=%08x %08x\n", c_sign, c_exp, (uint32_t)c_mant1, (uint32_t)c_mant0);

    /* ensure that abs(r) >= abs(c) */
    if (!(r_exp > c_exp || (r_exp == c_exp && r_mant1 >= c_mant1))) {
        F_UINT tmp;
        int32_t c_tmp;
        /* swap */
        tmp = r_mant1; r_mant1 = c_mant1; c_mant1 = tmp;
        tmp = r_mant0; r_mant0 = c_mant0; c_mant0 = tmp;
        c_tmp = r_exp; r_exp = c_exp; c_exp = c_tmp;
        c_tmp = r_sign; r_sign = c_sign; c_sign = c_tmp;
    }
    /* right shift c_mant */
    shift = r_exp - c_exp;
    if (shift >= 2 * F_SIZE) {
        c_mant0 = (c_mant0 | c_mant1) != 0;
        c_mant1 = 0;
    } else if (shift >= F_SIZE + 1) {
        c_mant0 = rshift_rnd(c_mant1, shift - F_SIZE);
        c_mant1 = 0;
    } else if (shift == F_SIZE) {
        c_mant0 = c_mant1 | (c_mant0 != 0);
        c_mant1 = 0;
    } else if (shift != 0) {
        mask = ((F_UINT)1 << shift) - 1;
        c_mant0 = (c_mant1 << (F_SIZE - shift)) | (c_mant0 >> shift) | ((c_mant0 & mask) != 0);
        c_mant1 = c_mant1 >> shift;
    }
    //    printf("  r_mant=%08x %08x\n", (uint32_t)r_mant1, (uint32_t)r_mant0);
    //    printf("  c_mant=%08x %08x\n", (uint32_t)c_mant1, (uint32_t)c_mant0);
    /* add or subtract */
    if (r_sign == c_sign) {
        r_mant0 += c_mant0;
        r_mant1 += c_mant1 + (r_mant0 < c_mant0);
    } else {
        F_UINT tmp;
        tmp = r_mant0;
        r_mant0 -= c_mant0;
        r_mant1 = r_mant1 - c_mant1 - (r_mant0 > tmp);
        if ((r_mant0 | r_mant1) == 0) {
            /* zero result : the sign needs a specific handling */
            r_sign = (rm == RM_RDN);
        }
    }
#if 0
    //    printf("  r1_mant=%08x %08x\n", (uint32_t)r_mant1, (uint32_t)r_mant0);
    /* normalize */
    if (r_mant1 == 0) {
        r_mant1 = r_mant0;
        r_exp -= F_SIZE;
    } else {
        shift = clz(r_mant1) - (F_SIZE - 1 - IMANT_SIZE);
        if (shift != 0) {
            r_mant1 = (r_mant1 << shift) | (r_mant0 >> (F_SIZE - shift));
            r_mant0 <<= shift;
            r_exp -= shift;
        }
        r_mant1 |= (r_mant0 != 0);
    }
    return normalize_sf(r_sign, r_exp, r_mant1, rm, pfflags);
#else
    return normalize2_sf(r_sign, r_exp, r_mant1, r_mant0, rm, pfflags);
#endif
}

#ifdef F_ULONG

static F_UINT divrem_u(F_UINT *pr, F_UINT ah, F_UINT al, F_UINT b)
{
    F_ULONG a;
    a = ((F_ULONG)ah << F_SIZE) | al;
    *pr = a % b;
    return a / b;
}

#else

static F_UINT divrem_u(F_UINT *pr, F_UINT a1, F_UINT a0, F_UINT b)
{
    int i, qb, ab;

    assert(a1 < b);
    for (i = 0; i < F_SIZE; i++) {
        ab = a1 >> (F_SIZE - 1);
        a1 = (a1 << 1) | (a0 >> (F_SIZE - 1));
        if (ab || a1 >= b) {
            a1 -= b;
            qb = 1;
        } else {
            qb = 0;
        }
        a0 = (a0 << 1) | qb;
    }
    *pr = a1;
    return a0;
}

#endif

F_UINT div_sf(F_UINT a, F_UINT b, RoundingModeEnum rm,
              uint32_t *pfflags)
{
    uint32_t a_sign, b_sign, r_sign;
    int32_t a_exp, b_exp, r_exp;
    F_UINT a_mant, b_mant, r_mant, r;

    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);
    r_sign = a_sign ^ b_sign;
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    b_exp = (b >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    b_mant = b & MANT_MASK;
    if (a_exp == EXP_MASK) {
        if (a_mant != 0 || isnan_sf(b)) {
            if (issignan_sf(a) || issignan_sf(b)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        } else if (b_exp == EXP_MASK) {
            *pfflags |= FFLAG_INVALID_OP;
            return F_QNAN;
        } else {
            return pack_sf(r_sign, EXP_MASK, 0);
        }
    } else if (b_exp == EXP_MASK) {
        if (b_mant != 0) {
            if (issignan_sf(a) || issignan_sf(b)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        } else {
            return pack_sf(r_sign, 0, 0);
        }
    }

    if (b_exp == 0) {
        if (b_mant == 0) {
            /* zero */
            if (a_exp == 0 && a_mant == 0) {
                *pfflags |= FFLAG_INVALID_OP;
                return F_QNAN;
            } else {
                *pfflags |= FFLAG_DIVIDE_ZERO;
                return pack_sf(r_sign, EXP_MASK, 0);
            }
        }
        b_mant = normalize_subnormal_sf(&b_exp, b_mant);
    } else {
        b_mant |= (F_UINT)1 << MANT_SIZE;
    }
    if (a_exp == 0) {
        if (a_mant == 0)
            return pack_sf(r_sign, 0, 0); /* zero */
        a_mant = normalize_subnormal_sf(&a_exp, a_mant);
    } else {
        a_mant |= (F_UINT)1 << MANT_SIZE;
    }
    r_exp = a_exp - b_exp + (1 << (EXP_SIZE - 1)) - 1;
    r_mant = divrem_u(&r, a_mant, 0, b_mant << 2);
    if (r != 0)
        r_mant |= 1;
    return normalize_sf(r_sign, r_exp, r_mant, rm, pfflags);
}

#ifdef F_ULONG

/* compute sqrt(a) with a = ah*2^F_SIZE+al and a < 2^(F_SIZE - 2)
   return true if not exact square. */
static int sqrtrem_u(F_UINT *pr, F_UINT ah, F_UINT al)
{
    F_ULONG a, u, s;
    int l, inexact;

    /* 2^l >= a */
    if (ah != 0) {
        l = 2 * F_SIZE - clz(ah - 1);
    } else {
        if (al == 0) {
            *pr = 0;
            return 0;
        }
        l = F_SIZE - clz(al - 1);
    }
    a = ((F_ULONG)ah << F_SIZE) | al;
    u = (F_ULONG)1 << ((l + 1) / 2);
    for (;;) {
        s = u;
        u = ((a / s) + s) / 2;
        if (u >= s)
            break;
    }
    inexact = (a - s * s) != 0;
    *pr = s;
    return inexact;
}

#else

static int sqrtrem_u(F_UINT *pr, F_UINT a1, F_UINT a0)
{
    int l, inexact;
    F_UINT u, s, r, q, sq0, sq1;

    /* 2^l >= a */
    if (a1 != 0) {
        l = 2 * F_SIZE - clz(a1 - 1);
    } else {
        if (a0 == 0) {
            *pr = 0;
            return 0;
        }
        l = F_SIZE - clz(a0 - 1);
    }
    u = (F_UINT)1 << ((l + 1) / 2);
    for (;;) {
        s = u;
        q = divrem_u(&r, a1, a0, s);
        u = (q + s) / 2;
        if (u >= s)
            break;
    }
    sq1 = mul_u(&sq0, s, s);
    inexact = (sq0 != a0 || sq1 != a1);
    *pr = s;
    return inexact;
}

#endif

F_UINT sqrt_sf(F_UINT a, RoundingModeEnum rm,
               uint32_t *pfflags)
{
    uint32_t a_sign;
    int32_t a_exp;
    F_UINT a_mant;

    a_sign = a >> (F_SIZE - 1);
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    if (a_exp == EXP_MASK) {
        if (a_mant != 0) {
            if (issignan_sf(a)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        } else if (a_sign) {
            goto neg_error;
        } else {
            return a; /* +infinity */
        }
    }
    if (a_sign) {
        if (a_exp == 0 && a_mant == 0)
            return a; /* -zero */
    neg_error:
        *pfflags |= FFLAG_INVALID_OP;
        return F_QNAN;
    }
    if (a_exp == 0) {
        if (a_mant == 0)
            return pack_sf(0, 0, 0); /* zero */
        a_mant = normalize_subnormal_sf(&a_exp, a_mant);
    } else {
        a_mant |= (F_UINT)1 << MANT_SIZE;
    }
    a_exp -= EXP_MASK / 2;
    /* simpler to handle an even exponent */
    if (a_exp & 1) {
        a_exp--;
        a_mant <<= 1;
    }
    a_exp = (a_exp >> 1) + EXP_MASK / 2;
    a_mant <<= (F_SIZE - 4 - MANT_SIZE);
    if (sqrtrem_u(&a_mant, a_mant, 0))
        a_mant |= 1;
    return normalize_sf(a_sign, a_exp, a_mant, rm, pfflags);
}

/* comparisons */

F_UINT glue(min_sf, F_SIZE)(F_UINT a, F_UINT b, uint32_t *pfflags)
{
    uint32_t a_sign, b_sign;

    if (isnan_sf(a) || isnan_sf(b)) {
        if (issignan_sf(a) || issignan_sf(b)) {
            *pfflags |= FFLAG_INVALID_OP;
            /* RISC-V User ISA 2.2 used to return a QNaN, but
             * follows Java/IEEE 754-201x from 2.3 onwards
             * return F_QNAN;
             */
        }
        if (isnan_sf(a)) {
            if (isnan_sf(b))
                return F_QNAN;
            else
                return b;
        } else {
            return a;
        }
    }
    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);

    if (a_sign != b_sign) {
        if (a_sign)
            return a;
        else
            return b;
    } else {
        if ((a < b) ^ a_sign)
            return a;
        else
            return b;
    }
}

F_UINT glue(max_sf, F_SIZE)(F_UINT a, F_UINT b, uint32_t *pfflags)
{
    uint32_t a_sign, b_sign;

    if (isnan_sf(a) || isnan_sf(b)) {
        if (issignan_sf(a) || issignan_sf(b)) {
            *pfflags |= FFLAG_INVALID_OP;
            /* RISC-V User ISA 2.2 used to return a QNaN, but
             * follows Java/IEEE 754-201x from 2.3 onwards
             * return F_QNAN;
             */
        }
        if (isnan_sf(a)) {
            if (isnan_sf(b))
                return F_QNAN;
            else
                return b;
        } else {
            return a;
        }
    }
    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);

    if (a_sign != b_sign) {
        if (a_sign)
            return b;
        else
            return a;
    } else {
        if ((a < b) ^ a_sign)
            return b;
        else
            return a;
    }
}

int glue(eq_quiet_sf, F_SIZE)(F_UINT a, F_UINT b, uint32_t *pfflags)
{
    if (isnan_sf(a) || isnan_sf(b)) {
        if (issignan_sf(a) || issignan_sf(b)) {
            *pfflags |= FFLAG_INVALID_OP;
        }
        return 0;
    }

    if ((F_UINT)((a | b) << 1) == 0)
        return 1; /* zero case */
    return (a == b);
}

int glue(le_sf, F_SIZE)(F_UINT a, F_UINT b, uint32_t *pfflags)
{
    uint32_t a_sign, b_sign;

    if (isnan_sf(a) || isnan_sf(b)) {
        *pfflags |= FFLAG_INVALID_OP;
        return 0;
    }

    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);
    if (a_sign != b_sign) {
        return (a_sign || ((F_UINT)((a | b) << 1) == 0));
    } else {
        if (a_sign) {
            return (a >= b);
        } else {
            return (a <= b);
        }
    }
}

int glue(lt_sf, F_SIZE)(F_UINT a, F_UINT b, uint32_t *pfflags)
{
    uint32_t a_sign, b_sign;

    if (isnan_sf(a) || isnan_sf(b)) {
        *pfflags |= FFLAG_INVALID_OP;
        return 0;
    }

    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);
    if (a_sign != b_sign) {
        return (a_sign && ((F_UINT)((a | b) << 1) != 0));
    } else {
        if (a_sign) {
            return (a > b);
        } else {
            return (a < b);
        }
    }
}

uint32_t glue(fclass_sf, F_SIZE)(F_UINT a)
{
    uint32_t a_sign;
    int32_t a_exp;
    F_UINT a_mant;
    uint32_t ret;

    a_sign = a >> (F_SIZE - 1);
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    if (a_exp == EXP_MASK) {
        if (a_mant != 0) {
            if (a_mant & QNAN_MASK)
                ret = FCLASS_QNAN;
            else
                ret = FCLASS_SNAN;
        } else {
            if (a_sign)
                ret = FCLASS_NINF;
            else
                ret = FCLASS_PINF;
        }
    } else if (a_exp == 0) {
        if (a_mant == 0) {
            if (a_sign)
                ret = FCLASS_NZERO;
            else
                ret = FCLASS_PZERO;
        } else {
            if (a_sign)
                ret = FCLASS_NSUBNORMAL;
            else
                ret = FCLASS_PSUBNORMAL;
        }
    } else {
        if (a_sign)
            ret = FCLASS_NNORMAL;
        else
            ret = FCLASS_PNORMAL;
    }
    return ret;
}

/* conversions between floats */

#if F_SIZE >= 64

F_UINT cvt_sf32_sf(uint32_t a, uint32_t *pfflags)
{
    uint32_t a_sign;
    int32_t a_exp;
    F_UINT a_mant;

    a_mant = unpack_sf32(&a_sign, &a_exp, a);
    if (a_exp == 0xff) {
        if (a_mant != 0) {
            /* NaN */
            if (issignan_sf32(a)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        } else {
            /* infinity */
            return pack_sf(a_sign, EXP_MASK, 0);
        }
    }
    if (a_exp == 0) {
        if (a_mant == 0)
            return pack_sf(a_sign, 0, 0); /* zero */
        a_mant = normalize_subnormal_sf32(&a_exp, a_mant);
    }
    /* convert the exponent value */
    a_exp = a_exp - 0x7f + (EXP_MASK / 2);
    /* shift the mantissa */
    a_mant <<= (MANT_SIZE - 23);
    /* We assume the target float is large enough to that no
       normalization is necessary */
    return pack_sf(a_sign, a_exp, a_mant);
}

uint32_t glue(glue(cvt_sf, F_SIZE), _sf32)(F_UINT a, RoundingModeEnum rm,
                                           uint32_t *pfflags)
{
    uint32_t a_sign;
    int32_t a_exp;
    F_UINT a_mant;

    a_mant = unpack_sf(&a_sign, &a_exp, a);
    if (a_exp == EXP_MASK) {
        if (a_mant != 0) {
            /* NaN */
            if (issignan_sf(a)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN32;
        } else {
            /* infinity */
            return pack_sf32(a_sign, 0xff, 0);
        }
    }
    if (a_exp == 0) {
        if (a_mant == 0)
            return pack_sf32(a_sign, 0, 0); /* zero */
        normalize_subnormal_sf(&a_exp, a_mant);
    } else {
        a_mant |= (F_UINT)1 << MANT_SIZE;
    }
    /* convert the exponent value */
    a_exp = a_exp - (EXP_MASK / 2) + 0x7f;
    /* shift the mantissa */
    a_mant = rshift_rnd(a_mant, MANT_SIZE - (32 - 2));
    return normalize_sf32(a_sign, a_exp, a_mant, rm, pfflags);
}

#endif

#if F_SIZE >= 128

F_UINT cvt_sf64_sf(uint64_t a, uint32_t *pfflags)
{
    uint32_t a_sign;
    int32_t a_exp;
    F_UINT a_mant;

    a_mant = unpack_sf64(&a_sign, &a_exp, a);

    if (a_exp == 0x7ff) {
        if (a_mant != 0) {
            /* NaN */
            if (issignan_sf64(a)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        } else {
            /* infinity */
            return pack_sf(a_sign, EXP_MASK, 0);
        }
    }
    if (a_exp == 0) {
        if (a_mant == 0)
            return pack_sf(a_sign, 0, 0); /* zero */
        a_mant = normalize_subnormal_sf64(&a_exp, a_mant);
    }
    /* convert the exponent value */
    a_exp = a_exp - 0x3ff + (EXP_MASK / 2);
    /* shift the mantissa */
    a_mant <<= (MANT_SIZE - 52);
    return pack_sf(a_sign, a_exp, a_mant);
}

uint64_t glue(glue(cvt_sf, F_SIZE), _sf64)(F_UINT a, RoundingModeEnum rm,
                                               uint32_t *pfflags)
{
    uint32_t a_sign;
    int32_t a_exp;
    F_UINT a_mant;

    a_mant = unpack_sf(&a_sign, &a_exp, a);
    if (a_exp == EXP_MASK) {
        if (a_mant != 0) {
            /* NaN */
            if (issignan_sf(a)) {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN64;
        } else {
            /* infinity */
            return pack_sf64(a_sign, 0x7ff, 0);
        }
    }
    if (a_exp == 0) {
        if (a_mant == 0)
            return pack_sf64(a_sign, 0, 0); /* zero */
        normalize_subnormal_sf(&a_exp, a_mant);
    } else {
        a_mant |= (F_UINT)1 << MANT_SIZE;
    }
    /* convert the exponent value */
    a_exp = a_exp - (EXP_MASK / 2) + 0x3ff;
    /* shift the mantissa */
    a_mant = rshift_rnd(a_mant, MANT_SIZE - (64 - 2));
    return normalize_sf64(a_sign, a_exp, a_mant, rm, pfflags);
}

#endif

#undef clz

#define ICVT_SIZE 32
#include "softfp_template_icvt.h"

#define ICVT_SIZE 64
#include "softfp_template_icvt.h"

#ifdef HAVE_INT128
#define ICVT_SIZE 128
#include "softfp_template_icvt.h"
#endif

#undef F_SIZE
#undef F_UINT
#undef F_ULONG
#undef F_UHALF
#undef MANT_SIZE
#undef EXP_SIZE
#undef EXP_MASK
#undef MANT_MASK
#undef SIGN_MASK
#undef IMANT_SIZE
#undef RND_SIZE
#undef QNAN_MASK
#undef F_QNAN

#undef pack_sf
#undef unpack_sf
#undef rshift_rnd
#undef round_pack_sf
#undef normalize_sf
#undef normalize2_sf
#undef issignan_sf
#undef isnan_sf
#undef add_sf
#undef mul_sf
#undef fma_sf
#undef div_sf
#undef sqrt_sf
#undef normalize_subnormal_sf
#undef divrem_u
#undef sqrtrem_u
#undef mul_u
#undef cvt_sf32_sf
#undef cvt_sf64_sf
