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
#if ICVT_SIZE == 32
#define ICVT_UINT uint32_t
#define ICVT_INT int32_t
#elif ICVT_SIZE == 64
#define ICVT_UINT uint64_t
#define ICVT_INT int64_t
#elif ICVT_SIZE == 128
#define ICVT_UINT uint128_t
#define ICVT_INT int128_t
#else
#error unsupported icvt
#endif

/* conversions between float and integers */
static ICVT_INT glue(glue(glue(internal_cvt_sf, F_SIZE), _i), ICVT_SIZE)(F_UINT a, RoundingModeEnum rm,
                                                                         uint32_t *pfflags, BOOL is_unsigned)
{
    uint32_t a_sign, addend, rnd_bits;
    int32_t a_exp;
    F_UINT a_mant;
    ICVT_UINT r, r_max;

    a_sign = a >> (F_SIZE - 1);
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    if (a_exp == EXP_MASK && a_mant != 0)
        a_sign = 0; /* NaN is like +infinity */
    if (a_exp == 0) {
        a_exp = 1;
    } else {
        a_mant |= (F_UINT)1 << MANT_SIZE;
    }
    a_mant <<= RND_SIZE;
    a_exp = a_exp - (EXP_MASK / 2) - MANT_SIZE;

    if (is_unsigned)
        r_max = (ICVT_UINT)a_sign - 1;
    else
        r_max = ((ICVT_UINT)1 << (ICVT_SIZE - 1)) - (ICVT_UINT)(a_sign ^ 1);
    if (a_exp >= 0) {
        if (a_exp <= (ICVT_SIZE - 1 - MANT_SIZE)) {
            r = (ICVT_UINT)(a_mant >> RND_SIZE) << a_exp;
            if (r > r_max)
                goto overflow;
        } else {
        overflow:
            *pfflags |= FFLAG_INVALID_OP;
            return r_max;
        }
    } else {
        a_mant = rshift_rnd(a_mant, -a_exp);

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
            if (a_sign ^ (rm & 1))
                addend = (1 << RND_SIZE) - 1;
            else
                addend = 0;
            break;
        }

        rnd_bits = a_mant & ((1 << RND_SIZE ) - 1);
        a_mant = (a_mant + addend) >> RND_SIZE;
        /* half way: select even result */
        if (rm == RM_RNE && rnd_bits == (1 << (RND_SIZE - 1)))
            a_mant &= ~1;
        if (a_mant > r_max)
            goto overflow;
        r = a_mant;
        if (rnd_bits != 0)
            *pfflags |= FFLAG_INEXACT;
    }
    if (a_sign)
        r = -r;
    return r;
}

ICVT_INT glue(glue(glue(cvt_sf, F_SIZE), _i), ICVT_SIZE)(F_UINT a, RoundingModeEnum rm,
                                                          uint32_t *pfflags)
{
    return glue(glue(glue(internal_cvt_sf, F_SIZE), _i), ICVT_SIZE)(a, rm,
                                                                    pfflags, FALSE);
}

ICVT_UINT glue(glue(glue(cvt_sf, F_SIZE), _u), ICVT_SIZE)(F_UINT a, RoundingModeEnum rm,
                                                          uint32_t *pfflags)
{
    return glue(glue(glue(internal_cvt_sf, F_SIZE), _i), ICVT_SIZE) (a, rm,
                                                                     pfflags, TRUE);
}

/* conversions between float and integers */
static F_UINT glue(glue(glue(internal_cvt_i, ICVT_SIZE), _sf), F_SIZE)(ICVT_INT a,
                                                                       RoundingModeEnum rm,
                                                                       uint32_t *pfflags,
                                                                       BOOL is_unsigned)
{
    uint32_t a_sign;
    int32_t a_exp;
    F_UINT a_mant;
    ICVT_UINT r, mask;
    int l;

    if (!is_unsigned && a < 0) {
        a_sign = 1;
        r = -a;
    } else {
        a_sign = 0;
        r = a;
    }
    a_exp = (EXP_MASK / 2) + F_SIZE - 2;
    /* need to reduce range before generic float normalization */
    l = ICVT_SIZE - glue(clz, ICVT_SIZE)(r) - (F_SIZE - 1);
    if (l > 0) {
        mask = r & (((ICVT_UINT)1 << l) - 1);
        r = (r >> l) | ((r & mask) != 0);
        a_exp += l;
    }
    a_mant = r;
    return normalize_sf(a_sign, a_exp, a_mant, rm, pfflags);
}

F_UINT glue(glue(glue(cvt_i, ICVT_SIZE), _sf), F_SIZE)(ICVT_INT a,
                                                       RoundingModeEnum rm,
                                                       uint32_t *pfflags)
{
    return glue(glue(glue(internal_cvt_i, ICVT_SIZE), _sf), F_SIZE)(a, rm, pfflags, FALSE);
}

F_UINT glue(glue(glue(cvt_u, ICVT_SIZE), _sf), F_SIZE)(ICVT_UINT a,
                                                       RoundingModeEnum rm,
                                                       uint32_t *pfflags)
{
    return glue(glue(glue(internal_cvt_i, ICVT_SIZE), _sf), F_SIZE)(a, rm, pfflags, TRUE);
}

#undef ICVT_SIZE
#undef ICVT_INT
#undef ICVT_UINT
