/*
 * Floating-point operations.
 *
 * ==========================(LICENSE BEGIN)============================
 *
 * Copyright (c) 2017-2019  Falcon Project
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * ===========================(LICENSE END)=============================
 *
 * @author   Thomas Pornin <thomas.pornin@nccgroup.com>
 */

#if FALCON_FPEMU  // yyyFPEMU+1 yyyFPNATIVE+0

/* ====================================================================== */
/*
 * Custom floating-point implementation with integer arithmetics. We
 * use IEEE-754 "binary64" format, with some simplifications:
 *
 *   - Top bit is s = 1 for negative, 0 for positive.
 *
 *   - Exponent e uses the next 11 bits (bits 52 to 62, inclusive).
 *
 *   - Mantissa m uses the 52 low bits.
 *
 * Encoded value is, in general: (-1)^s * 2^(e-1023) * (1 + m*2^(-52))
 * i.e. the mantissa really is a 53-bit number (less than 2.0, but not
 * less than 1.0), but the top bit (equal to 1 by definition) is omitted
 * in the encoding.
 *
 * In IEEE-754, there are some special values:
 *
 *   - If e = 2047, then the value is either an infinite (m = 0) or
 *     a NaN (m != 0).
 *
 *   - If e = 0, then the value is either a zero (m = 0) or a subnormal,
 *     aka "denormalized number" (m != 0).
 *
 * Of these, we only need the zeros. The caller is responsible for not
 * providing operands that would lead to infinites, NaNs or subnormals.
 * If inputs are such that values go out of range, then indeterminate
 * values are returned (it would still be deterministic, but no specific
 * value may be relied upon).
 *
 * At the C level, the three parts are stored in a 64-bit unsigned
 * word.
 *
 * One may note that a property of the IEEE-754 format is that order
 * is preserved for positive values: if two positive floating-point
 * values x and y are such that x < y, then their respective encodings
 * as _signed_ 64-bit integers i64(x) and i64(y) will be such that
 * i64(x) < i64(y). For negative values, order is reversed: if x < 0,
 * y < 0, and x < y, then ia64(x) > ia64(y).
 *
 * IMPORTANT ASSUMPTIONS:
 * ======================
 *
 * For proper computations, and constant-time behaviour, we assume the
 * following:
 *
 *   - 32x32->64 multiplication (unsigned) has an execution time that
 *     is independent of its operands. This is true of most modern
 *     x86 and ARM cores. Notable exceptions are the ARM Cortex M0, M0+
 *     and M3 (in the M0 and M0+, this is done in software, so it depends
 *     on that routine), and the PowerPC cores from the G3/G4 lines.
 *     For more info, see: https://www.bearssl.org/ctmul.html
 *
 *   - Left-shifts and right-shifts of 32-bit values have an execution
 *     time which does not depend on the shifted value nor on the
 *     shift count. An historical exception is the Pentium IV, but most
 *     modern CPU have barrel shifters. Some small microcontrollers
 *     might have varying-time shifts (not the ARM Cortex M*, though).
 *
 *   - Right-shift of a signed negative value performs a sign extension.
 *     As per the C standard, this operation returns an
 *     implementation-defined result (this is NOT an "undefined
 *     behaviour"). On most/all systems, an arithmetic shift is
 *     performed, because this is what makes most sense.
 */

/*
 * Normally we should declare the 'fpr' type to be a struct or union
 * around the internal 64-bit value; however, we want to use the
 * direct 64-bit integer type to enable a lighter call convention on
 * ARM platforms. This means that direct (invalid) use of operators
 * such as '*' or '+' will not be caught by the compiler. We rely on
 * the "normal" (non-emulated) code to detect such instances.
 */
typedef uint64_t fpr;

/*
 * For computations, we split values into an integral mantissa in the
 * 2^54..2^55 range, and an (adjusted) exponent. The lowest bit is
 * "sticky" (it is set to 1 if any of the bits below it is 1); when
 * re-encoding, the low two bits are dropped, but may induce an
 * increment in the value for proper rounding.
 */

/*
 * Right-shift a 64-bit unsigned value by a possibly secret shift count.
 * We assumed that the underlying architecture had a barrel shifter for
 * 32-bit shifts, but for 64-bit shifts on a 32-bit system, this will
 * typically invoke a software routine that is not necessarily
 * constant-time; hence the function below.
 *
 * Shift count n MUST be in the 0..63 range.
 */
static inline uint64_t
fpr_ursh(uint64_t x, int n)
{
	x ^= (x ^ (x >> 32)) & -(uint64_t)(n >> 5);
	return x >> (n & 31);
}

/*
 * Right-shift a 64-bit signed value by a possibly secret shift count
 * (see fpr_ursh() for the rationale).
 *
 * Shift count n MUST be in the 0..63 range.
 */
static inline int64_t
fpr_irsh(int64_t x, int n)
{
	x ^= (x ^ (x >> 32)) & -(int64_t)(n >> 5);
	return x >> (n & 31);
}

/*
 * Left-shift a 64-bit unsigned value by a possibly secret shift count
 * (see fpr_ursh() for the rationale).
 *
 * Shift count n MUST be in the 0..63 range.
 */
static inline uint64_t
fpr_ulsh(uint64_t x, int n)
{
	x ^= (x ^ (x << 32)) & -(uint64_t)(n >> 5);
	return x << (n & 31);
}

/*
 * Expectations:
 *   s = 0 or 1
 *   exponent e is "arbitrary" and unbiased
 *   2^54 <= m < 2^55
 * Numerical value is (-1)^2 * m * 2^e
 *
 * Exponents which are too low lead to value zero. If the exponent is
 * too large, the returned value is indeterminate.
 *
 * If m = 0, then a zero is returned (using the provided sign).
 * If e < -1076, then a zero is returned (regardless of the value of m).
 * If e >= -1076 and e != 0, m must be within the expected range
 * (2^54 to 2^55-1).
 */
static inline fpr
FPR(int s, int e, uint64_t m)
{
	fpr x;
	uint32_t t;
	unsigned f;

	/*
	 * If e >= -1076, then the value is "normal"; otherwise, it
	 * should be a subnormal, which we clamp down to zero.
	 */
	e += 1076;
	t = (uint32_t)e >> 31;
	m &= (uint64_t)t - 1;

	/*
	 * If m = 0 then we want a zero; make e = 0 too, but conserve
	 * the sign.
	 */
	t = (uint32_t)(m >> 54);
	e &= -(int)t;

	/*
	 * The 52 mantissa bits come from m. Value m has its top bit set
	 * (unless it is a zero); we leave it "as is": the top bit will
	 * increment the exponent by 1, except when m = 0, which is
	 * exactly what we want.
	 */
	x = (((uint64_t)s << 63) | (m >> 2)) + ((uint64_t)(uint32_t)e << 52);

	/*
	 * Rounding: if the low three bits of m are 011, 110 or 111,
	 * then the value should be incremented to get the next
	 * representable value. This implements the usual
	 * round-to-nearest rule (with preference to even values in case
	 * of a tie). Note that the increment may make a carry spill
	 * into the exponent field, which is again exactly what we want
	 * in that case.
	 */
	f = (unsigned)m & 7U;
	x += (0xC8U >> f) & 1;
	return x;
}

#define fpr_scaled   Zf(fpr_scaled)
fpr fpr_scaled(int64_t i, int sc);

static inline fpr
fpr_of(int64_t i)
{
	return fpr_scaled(i, 0);
}

static const fpr fpr_q = 4667981563525332992;
static const fpr fpr_inverse_of_q = 4545632735260551042;
static const fpr fpr_inv_2sqrsigma0 = 4594603506513722306;
static const fpr fpr_inv_sigma[] = {
	0,  /* unused */
	4574611497772390042,
	4574501679055810265,
	4574396282908341804,
	4574245855758572086,
	4574103865040221165,
	4573969550563515544,
	4573842244705920822,
	4573721358406441454,
	4573606369665796042,
	4573496814039276259
};
static const fpr fpr_sigma_min[] = {
	0,  /* unused */
	4607707126469777035,
	4607777455861499430,
	4607846828256951418,
	4607949175006100261,
	4608049571757433526,
	4608148125896792003,
	4608244935301382692,
	4608340089478362016,
	4608433670533905013,
	4608525754002622308
};
static const fpr fpr_log2 = 4604418534313441775;
static const fpr fpr_inv_log2 = 4609176140021203710;
static const fpr fpr_bnorm_max = 4670353323383631276;
static const fpr fpr_zero = 0;
static const fpr fpr_one = 4607182418800017408;
static const fpr fpr_two = 4611686018427387904;
static const fpr fpr_onehalf = 4602678819172646912;
static const fpr fpr_invsqrt2 = 4604544271217802189;
static const fpr fpr_invsqrt8 = 4600040671590431693;
static const fpr fpr_ptwo31 = 4746794007248502784;
static const fpr fpr_ptwo31m1 = 4746794007244308480;
static const fpr fpr_mtwo31m1 = 13970166044099084288U;
static const fpr fpr_ptwo63m1 = 4890909195324358656;
static const fpr fpr_mtwo63m1 = 14114281232179134464U;
static const fpr fpr_ptwo63 = 4890909195324358656;

static inline int64_t
fpr_rint(fpr x)
{
	uint64_t m, d;
	int e;
	uint32_t s, dd, f;

	/*
	 * We assume that the value fits in -(2^63-1)..+(2^63-1). We can
	 * thus extract the mantissa as a 63-bit integer, then right-shift
	 * it as needed.
	 */
	m = ((x << 10) | ((uint64_t)1 << 62)) & (((uint64_t)1 << 63) - 1);
	e = 1085 - ((int)(x >> 52) & 0x7FF);

	/*
	 * If a shift of more than 63 bits is needed, then simply set m
	 * to zero. This also covers the case of an input operand equal
	 * to zero.
	 */
	m &= -(uint64_t)((uint32_t)(e - 64) >> 31);
	e &= 63;

	/*
	 * Right-shift m as needed. Shift count is e. Proper rounding
	 * mandates that:
	 *   - If the highest dropped bit is zero, then round low.
	 *   - If the highest dropped bit is one, and at least one of the
	 *     other dropped bits is one, then round up.
	 *   - If the highest dropped bit is one, and all other dropped
	 *     bits are zero, then round up if the lowest kept bit is 1,
	 *     or low otherwise (i.e. ties are broken by "rounding to even").
	 *
	 * We thus first extract a word consisting of all the dropped bit
	 * AND the lowest kept bit; then we shrink it down to three bits,
	 * the lowest being "sticky".
	 */
	d = fpr_ulsh(m, 63 - e);
	dd = (uint32_t)d | ((uint32_t)(d >> 32) & 0x1FFFFFFF);
	f = (uint32_t)(d >> 61) | ((dd | -dd) >> 31);
	m = fpr_ursh(m, e) + (uint64_t)((0xC8U >> f) & 1U);

	/*
	 * Apply the sign bit.
	 */
	s = (uint32_t)(x >> 63);
	return ((int64_t)m ^ -(int64_t)s) + (int64_t)s;
}

static inline int64_t
fpr_floor(fpr x)
{
	uint64_t t;
	int64_t xi;
	int e, cc;

	/*
	 * We extract the integer as a _signed_ 64-bit integer with
	 * a scaling factor. Since we assume that the value fits
	 * in the -(2^63-1)..+(2^63-1) range, we can left-shift the
	 * absolute value to make it in the 2^62..2^63-1 range: we
	 * will only need a right-shift afterwards.
	 */
	e = (int)(x >> 52) & 0x7FF;
	t = x >> 63;
	xi = (int64_t)(((x << 10) | ((uint64_t)1 << 62))
		& (((uint64_t)1 << 63) - 1));
	xi = (xi ^ -(int64_t)t) + (int64_t)t;
	cc = 1085 - e;

	/*
	 * We perform an arithmetic right-shift on the value. This
	 * applies floor() semantics on both positive and negative values
	 * (rounding toward minus infinity).
	 */
	xi = fpr_irsh(xi, cc & 63);

	/*
	 * If the true shift count was 64 or more, then we should instead
	 * replace xi with 0 (if nonnegative) or -1 (if negative). Edge
	 * case: -0 will be floored to -1, not 0 (whether this is correct
	 * is debatable; in any case, the other functions normalize zero
	 * to +0).
	 *
	 * For an input of zero, the non-shifted xi was incorrect (we used
	 * a top implicit bit of value 1, not 0), but this does not matter
	 * since this operation will clamp it down.
	 */
	xi ^= (xi ^ -(int64_t)t) & -(int64_t)((uint32_t)(63 - cc) >> 31);
	return xi;
}

static inline int64_t
fpr_trunc(fpr x)
{
	uint64_t t, xu;
	int e, cc;

	/*
	 * Extract the absolute value. Since we assume that the value
	 * fits in the -(2^63-1)..+(2^63-1) range, we can left-shift
	 * the absolute value into the 2^62..2^63-1 range, and then
	 * do a right shift afterwards.
	 */
	e = (int)(x >> 52) & 0x7FF;
	xu = ((x << 10) | ((uint64_t)1 << 62)) & (((uint64_t)1 << 63) - 1);
	cc = 1085 - e;
	xu = fpr_ursh(xu, cc & 63);

	/*
	 * If the exponent is too low (cc > 63), then the shift was wrong
	 * and we must clamp the value to 0. This also covers the case
	 * of an input equal to zero.
	 */
	xu &= -(uint64_t)((uint32_t)(cc - 64) >> 31);

	/*
	 * Apply back the sign, if the source value is negative.
	 */
	t = x >> 63;
	xu = (xu ^ -t) + t;
	return *(int64_t *)&xu;
}

#define fpr_add   Zf(fpr_add)
fpr fpr_add(fpr x, fpr y);

static inline fpr
fpr_sub(fpr x, fpr y)
{
	y ^= (uint64_t)1 << 63;
	return fpr_add(x, y);
}

static inline fpr
fpr_neg(fpr x)
{
	x ^= (uint64_t)1 << 63;
	return x;
}

static inline fpr
fpr_half(fpr x)
{
	/*
	 * To divide a value by 2, we just have to subtract 1 from its
	 * exponent, but we have to take care of zero.
	 */
	uint32_t t;

	x -= (uint64_t)1 << 52;
	t = (((uint32_t)(x >> 52) & 0x7FF) + 1) >> 11;
	x &= (uint64_t)t - 1;
	return x;
}

static inline fpr
fpr_double(fpr x)
{
	/*
	 * To double a value, we just increment by one the exponent. We
	 * don't care about infinites or NaNs; however, 0 is a
	 * special case.
	 */
	x += (uint64_t)((((unsigned)(x >> 52) & 0x7FFU) + 0x7FFU) >> 11) << 52;
	return x;
}

#define fpr_mul   Zf(fpr_mul)
fpr fpr_mul(fpr x, fpr y);

static inline fpr
fpr_sqr(fpr x)
{
	return fpr_mul(x, x);
}

#define fpr_div   Zf(fpr_div)
fpr fpr_div(fpr x, fpr y);

static inline fpr
fpr_inv(fpr x)
{
	return fpr_div(4607182418800017408u, x);
}

#define fpr_sqrt   Zf(fpr_sqrt)
fpr fpr_sqrt(fpr x);

static inline int
fpr_lt(fpr x, fpr y)
{
	/*
	 * If x >= 0 or y >= 0, a signed comparison yields the proper
	 * result:
	 *   - For positive values, the order is preserved.
	 *   - The sign bit is at the same place as in integers, so
	 *     sign is preserved.
	 *
	 * If both x and y are negative, then the order is reversed.
	 * We cannot simply invert the comparison result in that case
	 * because it would not handle the edge case x = y properly.
	 */
	int cc0, cc1;

	cc0 = *(int64_t *)&x < *(int64_t *)&y;
	cc1 = *(int64_t *)&x > *(int64_t *)&y;
	return cc0 ^ ((cc0 ^ cc1) & (int)((x & y) >> 63));
}

/*
 * Compute exp(x) for x such that |x| <= ln 2. We want a precision of 50
 * bits or so.
 */
#define fpr_expm_p63   Zf(fpr_expm_p63)
uint64_t fpr_expm_p63(fpr x, fpr ccs);

#define fpr_gm_tab   Zf(fpr_gm_tab)
extern const fpr fpr_gm_tab[];

#define fpr_p2_tab   Zf(fpr_p2_tab)
extern const fpr fpr_p2_tab[];

/* ====================================================================== */

#elif FALCON_FPNATIVE  // yyyFPEMU+0 yyyFPNATIVE+1

/* ====================================================================== */

#include <math.h>

/*
 * We wrap the native 'double' type into a structure so that the C compiler
 * complains if we inadvertently use raw arithmetic operators on the 'fpr'
 * type instead of using the inline functions below. This should have no
 * extra runtime cost, since all the functions below are 'inline'.
 */
typedef struct { double v; } fpr;

static inline fpr
FPR(double v)
{
	fpr x;

	x.v = v;
	return x;
}

static inline fpr
fpr_of(int64_t i)
{
	return FPR((double)i);
}

static const fpr fpr_q = { 12289.0 };
static const fpr fpr_inverse_of_q = { 1.0 / 12289.0 };
static const fpr fpr_inv_2sqrsigma0 = { .150865048875372721532312163019 };
static const fpr fpr_inv_sigma[] = {
	{ 0.0 }, /* unused */
	{ 0.0069054793295940891952143765991630516 },
	{ 0.0068102267767177975961393730687908629 },
	{ 0.0067188101910722710707826117910434131 },
	{ 0.0065883354370073665545865037227681924 },
	{ 0.0064651781207602900738053897763485516 },
	{ 0.0063486788828078995327741182928037856 },
	{ 0.0062382586529084374473367528433697537 },
	{ 0.0061334065020930261548984001431770281 },
	{ 0.0060336696681577241031668062510953022 },
	{ 0.0059386453095331159950250124336477482 }
};
static const fpr fpr_sigma_min[] = {
	{ 0.0 }, /* unused */
	{ 1.1165085072329102588881898380334015 },
	{ 1.1321247692325272405718031785357108 },
	{ 1.1475285353733668684571123112513188 },
	{ 1.1702540788534828939713084716509250 },
	{ 1.1925466358390344011122170489094133 },
	{ 1.2144300507766139921088487776957699 },
	{ 1.2359260567719808790104525941706723 },
	{ 1.2570545284063214162779743112075080 },
	{ 1.2778336969128335860256340575729042 },
	{ 1.2982803343442918539708792538826807 }
};
static const fpr fpr_log2 = { 0.69314718055994530941723212146 };
static const fpr fpr_inv_log2 = { 1.4426950408889634073599246810 };
static const fpr fpr_bnorm_max = { 16822.4121 };
static const fpr fpr_zero = { 0.0 };
static const fpr fpr_one = { 1.0 };
static const fpr fpr_two = { 2.0 };
static const fpr fpr_onehalf = { 0.5 };
static const fpr fpr_invsqrt2 = { 0.707106781186547524400844362105 };
static const fpr fpr_invsqrt8 = { 0.353553390593273762200422181052 };
static const fpr fpr_ptwo31 = { 2147483648.0 };
static const fpr fpr_ptwo31m1 = { 2147483647.0 };
static const fpr fpr_mtwo31m1 = { -2147483647.0 };
static const fpr fpr_ptwo63m1 = { 9223372036854775807.0 };
static const fpr fpr_mtwo63m1 = { -9223372036854775807.0 };
static const fpr fpr_ptwo63 = { 9223372036854775808.0 };

static inline int64_t
fpr_rint(fpr x)
{
	/*
	 * We do not want to use llrint() since it might be not
	 * constant-time.
	 *
	 * Suppose that x >= 0. If x >= 2^52, then it is already an
	 * integer. Otherwise, if x < 2^52, then computing x+2^52 will
	 * yield a value that will be rounded to the nearest integer
	 * with exactly the right rules (round-to-nearest-even).
	 *
	 * In order to have constant-time processing, we must do the
	 * computation for both x >= 0 and x < 0 cases, and use a
	 * cast to an integer to access the sign and select the proper
	 * value. Such casts also allow us to find out if |x| < 2^52.
	 */
	int64_t sx, tx, rp, rn, m;
	uint32_t ub;

	sx = (int64_t)(x.v - 1.0);
	tx = (int64_t)x.v;
	rp = (int64_t)(x.v + 4503599627370496.0) - 4503599627370496;
	rn = (int64_t)(x.v - 4503599627370496.0) + 4503599627370496;

	/*
	 * If tx >= 2^52 or tx < -2^52, then result is tx.
	 * Otherwise, if sx >= 0, then result is rp.
	 * Otherwise, result is rn. We use the fact that when x is
	 * close to 0 (|x| <= 0.25) then both rp and rn are correct;
	 * and if x is not close to 0, then trunc(x-1.0) yields the
	 * appropriate sign.
	 */

	/*
	 * Clamp rp to zero if tx < 0.
	 * Clamp rn to zero if tx >= 0.
	 */
	m = sx >> 63;
	rn &= m;
	rp &= ~m;

	/*
	 * Get the 12 upper bits of tx; if they are not all zeros or
	 * all ones, then tx >= 2^52 or tx < -2^52, and we clamp both
	 * rp and rn to zero. Otherwise, we clamp tx to zero.
	 */
	ub = (uint32_t)((uint64_t)tx >> 52);
	m = -(int64_t)((((ub + 1) & 0xFFF) - 2) >> 31);
	rp &= m;
	rn &= m;
	tx &= ~m;

	/*
	 * Only one of tx, rn or rp (at most) can be non-zero at this
	 * point.
	 */
	return tx | rn | rp;
}

static inline int64_t
fpr_floor(fpr x)
{
	int64_t r;

	/*
	 * The cast performs a trunc() (rounding toward 0) and thus is
	 * wrong by 1 for most negative values. The correction below is
	 * constant-time as long as the compiler turns the
	 * floating-point conversion result into a 0/1 integer without a
	 * conditional branch or another non-constant-time construction.
	 * This should hold on all modern architectures with an FPU (and
	 * if it is false on a given arch, then chances are that the FPU
	 * itself is not constant-time, making the point moot).
	 */
	r = (int64_t)x.v;
	return r - (x.v < (double)r);
}

static inline int64_t
fpr_trunc(fpr x)
{
	return (int64_t)x.v;
}

static inline fpr
fpr_add(fpr x, fpr y)
{
	return FPR(x.v + y.v);
}

static inline fpr
fpr_sub(fpr x, fpr y)
{
	return FPR(x.v - y.v);
}

static inline fpr
fpr_neg(fpr x)
{
	return FPR(-x.v);
}

static inline fpr
fpr_half(fpr x)
{
	return FPR(x.v * 0.5);
}

static inline fpr
fpr_double(fpr x)
{
	return FPR(x.v + x.v);
}

static inline fpr
fpr_mul(fpr x, fpr y)
{
	return FPR(x.v * y.v);
}

static inline fpr
fpr_sqr(fpr x)
{
	return FPR(x.v * x.v);
}

static inline fpr
fpr_inv(fpr x)
{
	return FPR(1.0 / x.v);
}

static inline fpr
fpr_div(fpr x, fpr y)
{
	return FPR(x.v / y.v);
}

#if FALCON_AVX2  // yyyAVX2+1
TARGET_AVX2
static inline void
fpr_sqrt_avx2(double *t)
{
	__m128d x;

	x = _mm_load1_pd(t);
	x = _mm_sqrt_pd(x);
	_mm_storel_pd(t, x);
}
#endif  // yyyAVX2-

static inline fpr
fpr_sqrt(fpr x)
{
	/*
	 * We prefer not to have a dependency on libm when it can be
	 * avoided. On x86, calling the sqrt() libm function inlines
	 * the relevant opcode (fsqrt or sqrtsd, depending on whether
	 * the 387 FPU or SSE2 is used for floating-point operations)
	 * but then makes an optional call to the library function
	 * for proper error handling, in case the operand is negative.
	 *
	 * To avoid this dependency, we use intrinsics or inline assembly
	 * on recognized platforms:
	 *
	 *  - If AVX2 is explicitly enabled, then we use SSE2 intrinsics.
	 *
	 *  - On GCC/Clang with SSE maths, we use SSE2 intrinsics.
	 *
	 *  - On GCC/Clang on i386, or MSVC on i386, we use inline assembly
	 *    to call the 387 FPU fsqrt opcode.
	 *
	 *  - On GCC/Clang/XLC on PowerPC, we use inline assembly to call
	 *    the fsqrt opcode (Clang needs a special hack).
	 *
	 *  - On GCC/Clang on ARM with hardware floating-point, we use
	 *    inline assembly to call the vqsrt.f64 opcode. Due to a
	 *    complex ecosystem of compilers and assembly syntaxes, we
	 *    have to call it "fsqrt" or "fsqrtd", depending on case.
	 *
	 * If the platform is not recognized, a call to the system
	 * library function sqrt() is performed. On some compilers, this
	 * may actually inline the relevant opcode, and call the library
	 * function only when the input is invalid (e.g. negative);
	 * Falcon never actually calls sqrt() on a negative value, but
	 * the dependency to libm will still be there.
	 */

#if FALCON_AVX2  // yyyAVX2+1
	fpr_sqrt_avx2(&x.v);
	return x;
#else  // yyyAVX2+0
#if defined __GNUC__ && defined __SSE2_MATH__
	return FPR(_mm_cvtsd_f64(_mm_sqrt_pd(_mm_set1_pd(x.v))));
#elif defined __GNUC__ && defined __i386__
	__asm__ __volatile__ (
		"fldl   %0\n\t"
		"fsqrt\n\t"
		"fstpl  %0\n\t"
		: "+m" (x.v) : : );
	return x;
#elif defined _M_IX86
	__asm {
		fld x.v
		fsqrt
		fstp x.v
	}
	return x;
#elif defined __PPC__ && defined __GNUC__
	fpr y;

#if defined __clang__
	/*
	 * Normally we should use a 'd' constraint (register that contains
	 * a 'double' value) but Clang 3.8.1 chokes on it. Instead we use
	 * an 'f' constraint, counting on the fact that 'float' values
	 * are managed in double-precision registers anyway, and the
	 * compiler will not add extra rounding steps.
	 */
	__asm__ ( "fsqrt  %0, %1" : "=f" (y.v) : "f" (x.v) : );
#else
	__asm__ ( "fsqrt  %0, %1" : "=d" (y.v) : "d" (x.v) : );
#endif
	return y;
#elif (defined __ARM_FP && ((__ARM_FP & 0x08) == 0x08)) \
	|| (!defined __ARM_FP && defined __ARM_VFPV2__)
	/*
	 * On ARM, assembly syntaxes are a bit of a mess, depending on
	 * whether GCC or Clang is used, and the binutils version, and
	 * whether this is 32-bit or 64-bit mode. The code below appears
	 * to work on:
	 *    32-bit   GCC-4.9.2   Clang-3.5   Binutils-2.25
	 *    64-bit   GCC-6.3.0   Clang-3.9   Binutils-2.28
	 */
#if defined __aarch64__ && __aarch64__
	__asm__ ( "fsqrt   %d0, %d0" : "+w" (x.v) : : );
#else
	__asm__ ( "fsqrtd  %P0, %P0" : "+w" (x.v) : : );
#endif
	return x;
#else
	return FPR(sqrt(x.v));
#endif
#endif  // yyyAVX2-
}

static inline int
fpr_lt(fpr x, fpr y)
{
	return x.v < y.v;
}

TARGET_AVX2
static inline uint64_t
fpr_expm_p63(fpr x, fpr ccs)
{
	/*
	 * Polynomial approximation of exp(-x) is taken from FACCT:
	 *   https://eprint.iacr.org/2018/1234
	 * Specifically, values are extracted from the implementation
	 * referenced from the FACCT article, and available at:
	 *   https://github.com/raykzhao/gaussian
	 * Tests over more than 24 billions of random inputs in the
	 * 0..log(2) range have never shown a deviation larger than
	 * 2^(-50) from the true mathematical value.
	 */

#if FALCON_AVX2  // yyyAVX2+1

	/*
	 * AVX2 implementation uses more operations than Horner's method,
	 * but with a lower expression tree depth. This helps because
	 * additions and multiplications have a latency of 4 cycles on
	 * a Skylake, but the CPU can issue two of them per cycle.
	 */

	static const union {
		double d[12];
		__m256d v[3];
	} c = {
		{
			0.999999999999994892974086724280,
			0.500000000000019206858326015208,
			0.166666666666984014666397229121,
			0.041666666666110491190622155955,
			0.008333333327800835146903501993,
			0.001388888894063186997887560103,
			0.000198412739277311890541063977,
			0.000024801566833585381209939524,
			0.000002755586350219122514855659,
			0.000000275607356160477811864927,
			0.000000025299506379442070029551,
			0.000000002073772366009083061987
		}
	};

	double d1, d2, d4, d8, y;
	__m256d d14, d58, d9c;

	d1 = -x.v;
	d2 = d1 * d1;
	d4 = d2 * d2;
	d8 = d4 * d4;
	d14 = _mm256_set_pd(d4, d2 * d1, d2, d1);
	d58 = _mm256_mul_pd(d14, _mm256_set1_pd(d4));
	d9c = _mm256_mul_pd(d14, _mm256_set1_pd(d8));
	d14 = _mm256_mul_pd(d14, _mm256_loadu_pd(&c.d[0]));
	d58 = FMADD(d58, _mm256_loadu_pd(&c.d[4]), d14);
	d9c = FMADD(d9c, _mm256_loadu_pd(&c.d[8]), d58);
	d9c = _mm256_hadd_pd(d9c, d9c);
	y = 1.0 + _mm_cvtsd_f64(_mm256_castpd256_pd128(d9c)) // _mm256_cvtsd_f64(d9c)
		+ _mm_cvtsd_f64(_mm256_extractf128_pd(d9c, 1));
	y *= ccs.v;

	/*
	 * Final conversion goes through int64_t first, because that's what
	 * the underlying opcode (vcvttsd2si) will do, and we know that the
	 * result will fit, since x >= 0 and ccs < 1. If we did the
	 * conversion directly to uint64_t, then the compiler would add some
	 * extra code to cover the case of a source value of 2^63 or more,
	 * and though the alternate path would never be exercised, the
	 * extra comparison would cost us some cycles.
	 */
	return (uint64_t)(int64_t)(y * fpr_ptwo63.v);

#else  // yyyAVX2+0

	/*
	 * Normal implementation uses Horner's method, which minimizes
	 * the number of operations.
	 */

	double d, y;

	d = x.v;
	y = 0.000000002073772366009083061987;
	y = 0.000000025299506379442070029551 - y * d;
	y = 0.000000275607356160477811864927 - y * d;
	y = 0.000002755586350219122514855659 - y * d;
	y = 0.000024801566833585381209939524 - y * d;
	y = 0.000198412739277311890541063977 - y * d;
	y = 0.001388888894063186997887560103 - y * d;
	y = 0.008333333327800835146903501993 - y * d;
	y = 0.041666666666110491190622155955 - y * d;
	y = 0.166666666666984014666397229121 - y * d;
	y = 0.500000000000019206858326015208 - y * d;
	y = 0.999999999999994892974086724280 - y * d;
	y = 1.000000000000000000000000000000 - y * d;
	y *= ccs.v;
	return (uint64_t)(y * fpr_ptwo63.v);

#endif  // yyyAVX2-
}

#define fpr_gm_tab   Zf(fpr_gm_tab)
extern const fpr fpr_gm_tab[];

#define fpr_p2_tab   Zf(fpr_p2_tab)
extern const fpr fpr_p2_tab[];

/* ====================================================================== */

#else  // yyyFPEMU+0 yyyFPNATIVE+0

#error No FP implementation selected

#endif  // yyyFPEMU- yyyFPNATIVE-
