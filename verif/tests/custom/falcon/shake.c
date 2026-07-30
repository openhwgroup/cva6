/*
 * SHAKE implementation.
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

#include <string.h>

#include "inner.h"

#if FALCON_ASM_CORTEXM4  // yyyASM_CORTEXM4+1

__attribute__((naked))
static void
process_block(uint64_t *A __attribute__((unused)))
{
	__asm__ (
	"push	{ r1, r2, r3, r4, r5, r6, r7, r8, r10, r11, r12, lr }\n\t"
	"sub	sp, sp, #232\n\t"
	"\n\t"
	"@ Invert some words (alternate internal representation, which\n\t"
	"@ saves some operations).\n\t"
	"\n\t"

#define INVERT_WORDS \
	"@ Invert A[1] and A[2].\n\t" \
	"adds	r1, r0, #8\n\t" \
	"ldm	r1, { r2, r3, r4, r5 }\n\t" \
	"mvns	r2, r2\n\t" \
	"mvns	r3, r3\n\t" \
	"mvns	r4, r4\n\t" \
	"mvns	r5, r5\n\t" \
	"stm	r1!, { r2, r3, r4, r5 }\n\t" \
	"@ Invert A[8]\n\t" \
	"adds	r1, r0, #64\n\t" \
	"ldm	r1, { r2, r3 }\n\t" \
	"mvns	r2, r2\n\t" \
	"mvns	r3, r3\n\t" \
	"stm	r1!, { r2, r3 }\n\t" \
	"@ Invert A[12]\n\t" \
	"adds	r1, r0, #96\n\t" \
	"ldm	r1, { r2, r3 }\n\t" \
	"mvns	r2, r2\n\t" \
	"mvns	r3, r3\n\t" \
	"stm	r1!, { r2, r3 }\n\t" \
	"@ Invert A[17]\n\t" \
	"adds	r1, r0, #136\n\t" \
	"ldm	r1, { r2, r3 }\n\t" \
	"mvns	r2, r2\n\t" \
	"mvns	r3, r3\n\t" \
	"stm	r1!, { r2, r3 }\n\t" \
	"@ Invert A[20]\n\t" \
	"adds	r1, r0, #160\n\t" \
	"ldm	r1, { r2, r3 }\n\t" \
	"mvns	r2, r2\n\t" \
	"mvns	r3, r3\n\t" \
	"stm	r1!, { r2, r3 }\n\t" \
	"\n\t"

	INVERT_WORDS

	"@ Do 24 rounds. Each loop iteration performs one rounds. We\n\t"
	"@ keep eight times the current round counter in [sp] (i.e.\n\t"
	"@ a multiple of 8, from 0 to 184).\n\t"
	"\n\t"
	"eors	r1, r1\n\t"
	"str	r1, [sp, #0]\n\t"
".process_block_loop:\n\t"
	"\n\t"
	"@ xor(A[5*i+0]) -> r1:r2\n\t"
	"@ xor(A[5*i+1]) -> r3:r4\n\t"
	"@ xor(A[5*i+2]) -> r5:r6\n\t"
	"@ xor(A[5*i+3]) -> r7:r8\n\t"
	"@ xor(A[5*i+4]) -> r10:r11\n\t"
	"ldm	r0!, { r1, r2, r3, r4, r5, r6, r7, r8 }\n\t"
	"adds	r0, #8\n\t"
	"ldm	r0!, { r10, r11, r12 }\n\t"
	"eors	r1, r10\n\t"
	"eors	r2, r11\n\t"
	"eors	r3, r12\n\t"
	"ldm	r0!, { r10, r11, r12 }\n\t"
	"eors	r4, r10\n\t"
	"eors	r5, r11\n\t"
	"eors	r6, r12\n\t"
	"ldm	r0!, { r10, r11 }\n\t"
	"eors	r7, r10\n\t"
	"eors	r8, r11\n\t"
	"adds	r0, #8\n\t"
	"ldm	r0!, { r10, r11, r12 }\n\t"
	"eors	r1, r10\n\t"
	"eors	r2, r11\n\t"
	"eors	r3, r12\n\t"
	"ldm	r0!, { r10, r11, r12 }\n\t"
	"eors	r4, r10\n\t"
	"eors	r5, r11\n\t"
	"eors	r6, r12\n\t"
	"ldm	r0!, { r10, r11 }\n\t"
	"eors	r7, r10\n\t"
	"eors	r8, r11\n\t"
	"adds	r0, #8\n\t"
	"ldm	r0!, { r10, r11, r12 }\n\t"
	"eors	r1, r10\n\t"
	"eors	r2, r11\n\t"
	"eors	r3, r12\n\t"
	"ldm	r0!, { r10, r11, r12 }\n\t"
	"eors	r4, r10\n\t"
	"eors	r5, r11\n\t"
	"eors	r6, r12\n\t"
	"ldm	r0!, { r10, r11 }\n\t"
	"eors	r7, r10\n\t"
	"eors	r8, r11\n\t"
	"adds	r0, #8\n\t"
	"ldm	r0!, { r10, r11, r12 }\n\t"
	"eors	r1, r10\n\t"
	"eors	r2, r11\n\t"
	"eors	r3, r12\n\t"
	"ldm	r0!, { r10, r11, r12 }\n\t"
	"eors	r4, r10\n\t"
	"eors	r5, r11\n\t"
	"eors	r6, r12\n\t"
	"ldm	r0!, { r10, r11 }\n\t"
	"eors	r7, r10\n\t"
	"eors	r8, r11\n\t"
	"ldm	r0!, { r10, r11 }\n\t"
	"subs	r0, #200\n\t"
	"ldr	r12, [r0, #32]\n\t"
	"eors	r10, r12\n\t"
	"ldr	r12, [r0, #36]\n\t"
	"eors	r11, r12\n\t"
	"ldr	r12, [r0, #72]\n\t"
	"eors	r10, r12\n\t"
	"ldr	r12, [r0, #76]\n\t"
	"eors	r11, r12\n\t"
	"ldr	r12, [r0, #112]\n\t"
	"eors	r10, r12\n\t"
	"ldr	r12, [r0, #116]\n\t"
	"eors	r11, r12\n\t"
	"ldr	r12, [r0, #152]\n\t"
	"eors	r10, r12\n\t"
	"ldr	r12, [r0, #156]\n\t"
	"eors	r11, r12\n\t"
	"\n\t"
	"@ t0 = xor(A[5*i+4]) ^ rotl1(xor(A[5*i+1])) -> r10:r11\n\t"
	"@ t1 = xor(A[5*i+0]) ^ rotl1(xor(A[5*i+2])) -> r1:r2\n\t"
	"@ t2 = xor(A[5*i+1]) ^ rotl1(xor(A[5*i+3])) -> r3:r4\n\t"
	"@ t3 = xor(A[5*i+2]) ^ rotl1(xor(A[5*i+4])) -> r5:r6\n\t"
	"@ t4 = xor(A[5*i+3]) ^ rotl1(xor(A[5*i+0])) -> r7:r8\n\t"
	"str	r11, [sp, #4]\n\t"
	"mov	r12, r10\n\t"
	"eors	r10, r10, r3, lsl #1\n\t"
	"eors	r10, r10, r4, lsr #31\n\t"
	"eors	r11, r11, r4, lsl #1\n\t"
	"eors	r11, r11, r3, lsr #31\n\t"
	"eors	r3, r3, r7, lsl #1\n\t"
	"eors	r3, r3, r8, lsr #31\n\t"
	"eors	r4, r4, r8, lsl #1\n\t"
	"eors	r4, r4, r7, lsr #31\n\t"
	"eors	r7, r7, r1, lsl #1\n\t"
	"eors	r7, r7, r2, lsr #31\n\t"
	"eors	r8, r8, r2, lsl #1\n\t"
	"eors	r8, r8, r1, lsr #31\n\t"
	"eors	r1, r1, r5, lsl #1\n\t"
	"eors	r1, r1, r6, lsr #31\n\t"
	"eors	r2, r2, r6, lsl #1\n\t"
	"eors	r2, r2, r5, lsr #31\n\t"
	"eors	r5, r5, r12, lsl #1\n\t"
	"eors	r6, r6, r12, lsr #31\n\t"
	"ldr	r12, [sp, #4]\n\t"
	"eors	r5, r5, r12, lsr #31\n\t"
	"eors	r6, r6, r12, lsl #1\n\t"
	"\n\t"
	"@ Save t2, t3 and t4 on the stack.\n\t"
	"addw	r12, sp, #4\n\t"
	"stm	r12, { r3, r4, r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ We XOR one of the t0..t4 values into each A[] word, and\n\t"
	"@ rotate the result by some amount (each word has its own\n\t"
	"@ amount). The results are written back into a stack buffer\n\t"
	"@ that starts at sp+32\n\t"
	"addw	r12, sp, #32\n\t"
	"\n\t"
	"@ XOR t0 into A[5*i+0] and t1 into A[5*i+1]; each A[i] is also\n\t"
	"@ rotated left by some amount.\n\t"
	"\n\t"
	"@ A[0] and A[1]\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r5, r10\n\t"
	"eors	r6, r11\n\t"
	"eors	r3, r7, r1\n\t"
	"eors	r4, r8, r2\n\t"
	"lsl	r7, r3, #1\n\t"
	"orr	r7, r7, r4, lsr #31\n\t"
	"lsl	r8, r4, #1\n\t"
	"orr	r8, r8, r3, lsr #31\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ A[5] and A[6]\n\t"
	"adds	r0, #24\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r3, r5, r10\n\t"
	"eors	r4, r6, r11\n\t"
	"lsl	r5, r4, #4\n\t"
	"orr	r5, r5, r3, lsr #28\n\t"
	"lsl	r6, r3, #4\n\t"
	"orr	r6, r6, r4, lsr #28\n\t"
	"eors	r3, r7, r1\n\t"
	"eors	r4, r8, r2\n\t"
	"lsl	r7, r4, #12\n\t"
	"orr	r7, r7, r3, lsr #20\n\t"
	"lsl	r8, r3, #12\n\t"
	"orr	r8, r8, r4, lsr #20\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ A[10] and A[11]\n\t"
	"adds	r0, #24\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r3, r5, r10\n\t"
	"eors	r4, r6, r11\n\t"
	"lsl	r5, r3, #3\n\t"
	"orr	r5, r5, r4, lsr #29\n\t"
	"lsl	r6, r4, #3\n\t"
	"orr	r6, r6, r3, lsr #29\n\t"
	"eors	r3, r7, r1\n\t"
	"eors	r4, r8, r2\n\t"
	"lsl	r7, r3, #10\n\t"
	"orr	r7, r7, r4, lsr #22\n\t"
	"lsl	r8, r4, #10\n\t"
	"orr	r8, r8, r3, lsr #22\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ A[15] and A[16]\n\t"
	"adds	r0, #24\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r3, r5, r10\n\t"
	"eors	r4, r6, r11\n\t"
	"lsl	r5, r4, #9\n\t"
	"orr	r5, r5, r3, lsr #23\n\t"
	"lsl	r6, r3, #9\n\t"
	"orr	r6, r6, r4, lsr #23\n\t"
	"eors	r3, r7, r1\n\t"
	"eors	r4, r8, r2\n\t"
	"lsl	r7, r4, #13\n\t"
	"orr	r7, r7, r3, lsr #19\n\t"
	"lsl	r8, r3, #13\n\t"
	"orr	r8, r8, r4, lsr #19\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ A[20] and A[21]\n\t"
	"adds	r0, #24\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r3, r5, r10\n\t"
	"eors	r4, r6, r11\n\t"
	"lsl	r5, r3, #18\n\t"
	"orr	r5, r5, r4, lsr #14\n\t"
	"lsl	r6, r4, #18\n\t"
	"orr	r6, r6, r3, lsr #14\n\t"
	"eors	r3, r7, r1\n\t"
	"eors	r4, r8, r2\n\t"
	"lsl	r7, r3, #2\n\t"
	"orr	r7, r7, r4, lsr #30\n\t"
	"lsl	r8, r4, #2\n\t"
	"orr	r8, r8, r3, lsr #30\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ XOR t2 into A[5*i+2] and t3 into A[5*i+3]; each A[i] is also\n\t"
	"@ rotated left by some amount. We reload t2 into r1:r2 and t3\n\t"
	"@ into r3:r4.\n\t"
	"addw	r5, sp, #4\n\t"
	"ldm	r5!, { r1, r2, r3, r4 }\n\t"
	"\n\t"
	"@ A[2] and A[3]\n\t"
	"subs	r0, #160\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r10, r5, r1\n\t"
	"eors	r11, r6, r2\n\t"
	"lsl	r5, r11, #30\n\t"
	"orr	r5, r5, r10, lsr #2\n\t"
	"lsl	r6, r10, #30\n\t"
	"orr	r6, r6, r11, lsr #2\n\t"
	"eors	r10, r7, r3\n\t"
	"eors	r11, r8, r4\n\t"
	"lsl	r7, r10, #28\n\t"
	"orr	r7, r7, r11, lsr #4\n\t"
	"lsl	r8, r11, #28\n\t"
	"orr	r8, r8, r10, lsr #4\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ A[7] and A[8]\n\t"
	"adds	r0, #24\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r10, r5, r1\n\t"
	"eors	r11, r6, r2\n\t"
	"lsl	r5, r10, #6\n\t"
	"orr	r5, r5, r11, lsr #26\n\t"
	"lsl	r6, r11, #6\n\t"
	"orr	r6, r6, r10, lsr #26\n\t"
	"eors	r10, r7, r3\n\t"
	"eors	r11, r8, r4\n\t"
	"lsl	r7, r11, #23\n\t"
	"orr	r7, r7, r10, lsr #9\n\t"
	"lsl	r8, r10, #23\n\t"
	"orr	r8, r8, r11, lsr #9\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ A[12] and A[13]\n\t"
	"adds	r0, #24\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r10, r5, r1\n\t"
	"eors	r11, r6, r2\n\t"
	"lsl	r5, r11, #11\n\t"
	"orr	r5, r5, r10, lsr #21\n\t"
	"lsl	r6, r10, #11\n\t"
	"orr	r6, r6, r11, lsr #21\n\t"
	"eors	r10, r7, r3\n\t"
	"eors	r11, r8, r4\n\t"
	"lsl	r7, r10, #25\n\t"
	"orr	r7, r7, r11, lsr #7\n\t"
	"lsl	r8, r11, #25\n\t"
	"orr	r8, r8, r10, lsr #7\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ A[17] and A[18]\n\t"
	"adds	r0, #24\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r10, r5, r1\n\t"
	"eors	r11, r6, r2\n\t"
	"lsl	r5, r10, #15\n\t"
	"orr	r5, r5, r11, lsr #17\n\t"
	"lsl	r6, r11, #15\n\t"
	"orr	r6, r6, r10, lsr #17\n\t"
	"eors	r10, r7, r3\n\t"
	"eors	r11, r8, r4\n\t"
	"lsl	r7, r10, #21\n\t"
	"orr	r7, r7, r11, lsr #11\n\t"
	"lsl	r8, r11, #21\n\t"
	"orr	r8, r8, r10, lsr #11\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ A[22] and A[23]\n\t"
	"adds	r0, #24\n\t"
	"ldm	r0!, { r5, r6, r7, r8 }\n\t"
	"eors	r10, r5, r1\n\t"
	"eors	r11, r6, r2\n\t"
	"lsl	r5, r11, #29\n\t"
	"orr	r5, r5, r10, lsr #3\n\t"
	"lsl	r6, r10, #29\n\t"
	"orr	r6, r6, r11, lsr #3\n\t"
	"eors	r10, r7, r3\n\t"
	"eors	r11, r8, r4\n\t"
	"lsl	r7, r11, #24\n\t"
	"orr	r7, r7, r10, lsr #8\n\t"
	"lsl	r8, r10, #24\n\t"
	"orr	r8, r8, r11, lsr #8\n\t"
	"stm	r12!, { r5, r6, r7, r8 }\n\t"
	"\n\t"
	"@ XOR t4 into A[5*i+4]; each A[i] is also rotated left by some\n\t"
	"@ amount. We reload t4 into r1:r2.\n\t"
	"ldr	r1, [sp, #20]\n\t"
	"ldr	r2, [sp, #24]\n\t"
	"\n\t"
	"@ A[4]\n\t"
	"subs	r0, #160\n\t"
	"ldm	r0!, { r5, r6 }\n\t"
	"eors	r3, r5, r1\n\t"
	"eors	r4, r6, r2\n\t"
	"lsl	r5, r3, #27\n\t"
	"orr	r5, r5, r4, lsr #5\n\t"
	"lsl	r6, r4, #27\n\t"
	"orr	r6, r6, r3, lsr #5\n\t"
	"stm	r12!, { r5, r6 }\n\t"
	"\n\t"
	"@ A[9]\n\t"
	"adds	r0, #32\n\t"
	"ldm	r0!, { r5, r6 }\n\t"
	"eors	r3, r5, r1\n\t"
	"eors	r4, r6, r2\n\t"
	"lsl	r5, r3, #20\n\t"
	"orr	r5, r5, r4, lsr #12\n\t"
	"lsl	r6, r4, #20\n\t"
	"orr	r6, r6, r3, lsr #12\n\t"
	"stm	r12!, { r5, r6 }\n\t"
	"\n\t"
	"@ A[14]\n\t"
	"adds	r0, #32\n\t"
	"ldm	r0!, { r5, r6 }\n\t"
	"eors	r3, r5, r1\n\t"
	"eors	r4, r6, r2\n\t"
	"lsl	r5, r4, #7\n\t"
	"orr	r5, r5, r3, lsr #25\n\t"
	"lsl	r6, r3, #7\n\t"
	"orr	r6, r6, r4, lsr #25\n\t"
	"stm	r12!, { r5, r6 }\n\t"
	"\n\t"
	"@ A[19]\n\t"
	"adds	r0, #32\n\t"
	"ldm	r0!, { r5, r6 }\n\t"
	"eors	r3, r5, r1\n\t"
	"eors	r4, r6, r2\n\t"
	"lsl	r5, r3, #8\n\t"
	"orr	r5, r5, r4, lsr #24\n\t"
	"lsl	r6, r4, #8\n\t"
	"orr	r6, r6, r3, lsr #24\n\t"
	"stm	r12!, { r5, r6 }\n\t"
	"\n\t"
	"@ A[24]\n\t"
	"adds	r0, #32\n\t"
	"ldm	r0!, { r5, r6 }\n\t"
	"eors	r3, r5, r1\n\t"
	"eors	r4, r6, r2\n\t"
	"lsl	r5, r3, #14\n\t"
	"orr	r5, r5, r4, lsr #18\n\t"
	"lsl	r6, r4, #14\n\t"
	"orr	r6, r6, r3, lsr #18\n\t"
	"stm	r12!, { r5, r6 }\n\t"
	"\n\t"
	"subs	r0, #200\n\t"
	"\n\t"
	"@ At that point, the stack buffer at sp+32 contains the words\n\t"
	"@ at the following indexes (0 to 24) and offsets (from sp)\n\t"
	"@   A[ 0]    0      32\n\t"
	"@   A[ 1]    1      40\n\t"
	"@   A[ 2]   10     112\n\t"
	"@   A[ 3]   11     120\n\t"
	"@   A[ 4]   20     192\n\t"
	"@   A[ 5]    2      48\n\t"
	"@   A[ 6]    3      56\n\t"
	"@   A[ 7]   12     128\n\t"
	"@   A[ 8]   13     136\n\t"
	"@   A[ 9]   21     200\n\t"
	"@   A[10]    4      64\n\t"
	"@   A[11]    5      72\n\t"
	"@   A[12]   14     144\n\t"
	"@   A[13]   15     152\n\t"
	"@   A[14]   22     208\n\t"
	"@   A[15]    6      80\n\t"
	"@   A[16]    7      88\n\t"
	"@   A[17]   16     160\n\t"
	"@   A[18]   17     168\n\t"
	"@   A[19]   23     216\n\t"
	"@   A[20]    8      96\n\t"
	"@   A[21]    9     104\n\t"
	"@   A[22]   18     176\n\t"
	"@   A[23]   19     184\n\t"
	"@   A[24]   24     224\n\t"

#define KHI_LOAD(s0, s1, s2, s3, s4) \
	"ldr	r1, [sp, #(32 + 8 * " #s0 ")]\n\t" \
	"ldr	r2, [sp, #(36 + 8 * " #s0 ")]\n\t" \
	"ldr	r3, [sp, #(32 + 8 * " #s1 ")]\n\t" \
	"ldr	r4, [sp, #(36 + 8 * " #s1 ")]\n\t" \
	"ldr	r5, [sp, #(32 + 8 * " #s2 ")]\n\t" \
	"ldr	r6, [sp, #(36 + 8 * " #s2 ")]\n\t" \
	"ldr	r7, [sp, #(32 + 8 * " #s3 ")]\n\t" \
	"ldr	r8, [sp, #(36 + 8 * " #s3 ")]\n\t" \
	"ldr	r10, [sp, #(32 + 8 * " #s4 ")]\n\t" \
	"ldr	r11, [sp, #(36 + 8 * " #s4 ")]\n\t"

#define KHI_STEP(op, x0, x1, x2, x3, x4, x5, d) \
	#op "	r12, " #x0 ", " #x2 "\n\t" \
	"eors	r12, " #x4 "\n\t" \
	"str	r12, [r0, #(8 * " #d ")]\n\t" \
	#op "	r12, " #x1 ", " #x3 "\n\t" \
	"eors	r12, " #x5 "\n\t" \
	"str	r12, [r0, #(4 + 8 * " #d ")]\n\t"

	"@ A[0], A[6], A[12], A[18] and A[24]\n\t"
	KHI_LOAD(0, 3, 14, 17, 24)
	KHI_STEP(orrs, r3, r4, r5, r6, r1, r2, 0)
	KHI_STEP(orns, r7, r8, r5, r6, r3, r4, 1)
	KHI_STEP(ands, r7, r8, r10, r11, r5, r6, 2)
	KHI_STEP(orrs, r1, r2, r10, r11, r7, r8, 3)
	KHI_STEP(ands, r1, r2, r3, r4, r10, r11, 4)
	"\n\t"

	"@ A[3], A[9], A[10], A[16] and A[22]\n\t"
	KHI_LOAD(11, 21, 4, 7, 18)
	KHI_STEP(orrs, r3, r4, r5, r6, r1, r2, 5)
	KHI_STEP(ands, r7, r8, r5, r6, r3, r4, 6)
	KHI_STEP(orns, r7, r8, r10, r11, r5, r6, 7)
	KHI_STEP(orrs, r1, r2, r10, r11, r7, r8, 8)
	KHI_STEP(ands, r1, r2, r3, r4, r10, r11, 9)
	"\n\t"

	"@ A[1], A[7], A[13], A[19] and A[20]\n\t"
	KHI_LOAD(1, 12, 15, 23, 8)
	KHI_STEP(orrs, r3, r4, r5, r6, r1, r2, 10)
	KHI_STEP(ands, r7, r8, r5, r6, r3, r4, 11)
	KHI_STEP(bics, r10, r11, r7, r8, r5, r6, 12)
	"mvns	r7, r7\n\t"
	"mvns	r8, r8\n\t"
	KHI_STEP(orrs, r1, r2, r10, r11, r7, r8, 13)
	KHI_STEP(ands, r1, r2, r3, r4, r10, r11, 14)
	"\n\t"

	"@ A[4], A[5], A[11], A[17] and A[23]\n\t"
	KHI_LOAD(20, 2, 5, 16, 19)
	KHI_STEP(ands, r3, r4, r5, r6, r1, r2, 15)
	KHI_STEP(orrs, r7, r8, r5, r6, r3, r4, 16)
	KHI_STEP(orns, r10, r11, r7, r8, r5, r6, 17)
	"mvns	r7, r7\n\t"
	"mvns	r8, r8\n\t"
	KHI_STEP(ands, r1, r2, r10, r11, r7, r8, 18)
	KHI_STEP(orrs, r1, r2, r3, r4, r10, r11, 19)
	"\n\t"

	"@ A[2], A[8], A[14], A[15] and A[21]\n\t"
	KHI_LOAD(10, 13, 22, 6, 9)
	KHI_STEP(bics, r5, r6, r3, r4, r1, r2, 20)
	KHI_STEP(ands, r1, r2, r3, r4, r10, r11, 24)
	"mvns	r3, r3\n\t"
	"mvns	r4, r4\n\t"
	KHI_STEP(orrs, r7, r8, r5, r6, r3, r4, 21)
	KHI_STEP(ands, r7, r8, r10, r11, r5, r6, 22)
	KHI_STEP(orrs, r1, r2, r10, r11, r7, r8, 23)
	"\n\t"

	"@ Get round counter XOR round constant into A[0]\n\t"
	"ldr	r1, [sp, #0]\n\t"
	"adr	r2, .process_block_RC\n\t"
	"adds	r2, r1\n\t"
	"ldm	r2, { r3, r4 }\n\t"
	"ldm	r0, { r5, r6 }\n\t"
	"eors	r5, r3\n\t"
	"eors	r6, r4\n\t"
	"stm	r0, { r5, r6 }\n\t"
	"\n\t"
	"@ Increment round counter, loop until all 24 rounds are done.\n\t"
	"\n\t"
	"adds	r1, #8\n\t"
	"str	r1, [sp, #0]\n\t"
	"cmp	r1, #192\n\t"
	"blo	.process_block_loop\n\t"

	INVERT_WORDS

	"add	sp, sp, #232\n\t"
	"pop	{ r1, r2, r3, r4, r5, r6, r7, r8, r10, r11, r12, pc }\n\t"
	"\n\t"
".process_block_RC:\n\t"
	".word	0x00000001\n\t"
	".word	0x00000000\n\t"
	".word	0x00008082\n\t"
	".word	0x00000000\n\t"
	".word	0x0000808A\n\t"
	".word	0x80000000\n\t"
	".word	0x80008000\n\t"
	".word	0x80000000\n\t"
	".word	0x0000808B\n\t"
	".word	0x00000000\n\t"
	".word	0x80000001\n\t"
	".word	0x00000000\n\t"
	".word	0x80008081\n\t"
	".word	0x80000000\n\t"
	".word	0x00008009\n\t"
	".word	0x80000000\n\t"
	".word	0x0000008A\n\t"
	".word	0x00000000\n\t"
	".word	0x00000088\n\t"
	".word	0x00000000\n\t"
	".word	0x80008009\n\t"
	".word	0x00000000\n\t"
	".word	0x8000000A\n\t"
	".word	0x00000000\n\t"
	".word	0x8000808B\n\t"
	".word	0x00000000\n\t"
	".word	0x0000008B\n\t"
	".word	0x80000000\n\t"
	".word	0x00008089\n\t"
	".word	0x80000000\n\t"
	".word	0x00008003\n\t"
	".word	0x80000000\n\t"
	".word	0x00008002\n\t"
	".word	0x80000000\n\t"
	".word	0x00000080\n\t"
	".word	0x80000000\n\t"
	".word	0x0000800A\n\t"
	".word	0x00000000\n\t"
	".word	0x8000000A\n\t"
	".word	0x80000000\n\t"
	".word	0x80008081\n\t"
	".word	0x80000000\n\t"
	".word	0x00008080\n\t"
	".word	0x80000000\n\t"
	".word	0x80000001\n\t"
	".word	0x00000000\n\t"
	".word	0x80008008\n\t"
	".word	0x80000000\n\t"

#undef INVERT_WORDS
#undef KHI_LOAD
#undef KHI_STEP

	);
}

#else  // yyyASM_CORTEXM4+0

/*
 * Round constants.
 */
static const uint64_t RC[] = {
	0x0000000000000001, 0x0000000000008082,
	0x800000000000808A, 0x8000000080008000,
	0x000000000000808B, 0x0000000080000001,
	0x8000000080008081, 0x8000000000008009,
	0x000000000000008A, 0x0000000000000088,
	0x0000000080008009, 0x000000008000000A,
	0x000000008000808B, 0x800000000000008B,
	0x8000000000008089, 0x8000000000008003,
	0x8000000000008002, 0x8000000000000080,
	0x000000000000800A, 0x800000008000000A,
	0x8000000080008081, 0x8000000000008080,
	0x0000000080000001, 0x8000000080008008
};

/*
 * Process the provided state.
 */
static void
process_block(uint64_t *A)
{
	uint64_t t0, t1, t2, t3, t4;
	uint64_t tt0, tt1, tt2, tt3;
	uint64_t t, kt;
	uint64_t c0, c1, c2, c3, c4, bnn;
	int j;

	/*
	 * Invert some words (alternate internal representation, which
	 * saves some operations).
	 */
	A[ 1] = ~A[ 1];
	A[ 2] = ~A[ 2];
	A[ 8] = ~A[ 8];
	A[12] = ~A[12];
	A[17] = ~A[17];
	A[20] = ~A[20];

	/*
	 * Compute the 24 rounds. This loop is partially unrolled (each
	 * iteration computes two rounds).
	 */
	for (j = 0; j < 24; j += 2) {

		tt0 = A[ 1] ^ A[ 6];
		tt1 = A[11] ^ A[16];
		tt0 ^= A[21] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[ 4] ^ A[ 9];
		tt3 = A[14] ^ A[19];
		tt0 ^= A[24];
		tt2 ^= tt3;
		t0 = tt0 ^ tt2;

		tt0 = A[ 2] ^ A[ 7];
		tt1 = A[12] ^ A[17];
		tt0 ^= A[22] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[ 0] ^ A[ 5];
		tt3 = A[10] ^ A[15];
		tt0 ^= A[20];
		tt2 ^= tt3;
		t1 = tt0 ^ tt2;

		tt0 = A[ 3] ^ A[ 8];
		tt1 = A[13] ^ A[18];
		tt0 ^= A[23] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[ 1] ^ A[ 6];
		tt3 = A[11] ^ A[16];
		tt0 ^= A[21];
		tt2 ^= tt3;
		t2 = tt0 ^ tt2;

		tt0 = A[ 4] ^ A[ 9];
		tt1 = A[14] ^ A[19];
		tt0 ^= A[24] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[ 2] ^ A[ 7];
		tt3 = A[12] ^ A[17];
		tt0 ^= A[22];
		tt2 ^= tt3;
		t3 = tt0 ^ tt2;

		tt0 = A[ 0] ^ A[ 5];
		tt1 = A[10] ^ A[15];
		tt0 ^= A[20] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[ 3] ^ A[ 8];
		tt3 = A[13] ^ A[18];
		tt0 ^= A[23];
		tt2 ^= tt3;
		t4 = tt0 ^ tt2;

		A[ 0] = A[ 0] ^ t0;
		A[ 5] = A[ 5] ^ t0;
		A[10] = A[10] ^ t0;
		A[15] = A[15] ^ t0;
		A[20] = A[20] ^ t0;
		A[ 1] = A[ 1] ^ t1;
		A[ 6] = A[ 6] ^ t1;
		A[11] = A[11] ^ t1;
		A[16] = A[16] ^ t1;
		A[21] = A[21] ^ t1;
		A[ 2] = A[ 2] ^ t2;
		A[ 7] = A[ 7] ^ t2;
		A[12] = A[12] ^ t2;
		A[17] = A[17] ^ t2;
		A[22] = A[22] ^ t2;
		A[ 3] = A[ 3] ^ t3;
		A[ 8] = A[ 8] ^ t3;
		A[13] = A[13] ^ t3;
		A[18] = A[18] ^ t3;
		A[23] = A[23] ^ t3;
		A[ 4] = A[ 4] ^ t4;
		A[ 9] = A[ 9] ^ t4;
		A[14] = A[14] ^ t4;
		A[19] = A[19] ^ t4;
		A[24] = A[24] ^ t4;
		A[ 5] = (A[ 5] << 36) | (A[ 5] >> (64 - 36));
		A[10] = (A[10] <<  3) | (A[10] >> (64 -  3));
		A[15] = (A[15] << 41) | (A[15] >> (64 - 41));
		A[20] = (A[20] << 18) | (A[20] >> (64 - 18));
		A[ 1] = (A[ 1] <<  1) | (A[ 1] >> (64 -  1));
		A[ 6] = (A[ 6] << 44) | (A[ 6] >> (64 - 44));
		A[11] = (A[11] << 10) | (A[11] >> (64 - 10));
		A[16] = (A[16] << 45) | (A[16] >> (64 - 45));
		A[21] = (A[21] <<  2) | (A[21] >> (64 - 2));
		A[ 2] = (A[ 2] << 62) | (A[ 2] >> (64 - 62));
		A[ 7] = (A[ 7] <<  6) | (A[ 7] >> (64 -  6));
		A[12] = (A[12] << 43) | (A[12] >> (64 - 43));
		A[17] = (A[17] << 15) | (A[17] >> (64 - 15));
		A[22] = (A[22] << 61) | (A[22] >> (64 - 61));
		A[ 3] = (A[ 3] << 28) | (A[ 3] >> (64 - 28));
		A[ 8] = (A[ 8] << 55) | (A[ 8] >> (64 - 55));
		A[13] = (A[13] << 25) | (A[13] >> (64 - 25));
		A[18] = (A[18] << 21) | (A[18] >> (64 - 21));
		A[23] = (A[23] << 56) | (A[23] >> (64 - 56));
		A[ 4] = (A[ 4] << 27) | (A[ 4] >> (64 - 27));
		A[ 9] = (A[ 9] << 20) | (A[ 9] >> (64 - 20));
		A[14] = (A[14] << 39) | (A[14] >> (64 - 39));
		A[19] = (A[19] <<  8) | (A[19] >> (64 -  8));
		A[24] = (A[24] << 14) | (A[24] >> (64 - 14));

		bnn = ~A[12];
		kt = A[ 6] | A[12];
		c0 = A[ 0] ^ kt;
		kt = bnn | A[18];
		c1 = A[ 6] ^ kt;
		kt = A[18] & A[24];
		c2 = A[12] ^ kt;
		kt = A[24] | A[ 0];
		c3 = A[18] ^ kt;
		kt = A[ 0] & A[ 6];
		c4 = A[24] ^ kt;
		A[ 0] = c0;
		A[ 6] = c1;
		A[12] = c2;
		A[18] = c3;
		A[24] = c4;
		bnn = ~A[22];
		kt = A[ 9] | A[10];
		c0 = A[ 3] ^ kt;
		kt = A[10] & A[16];
		c1 = A[ 9] ^ kt;
		kt = A[16] | bnn;
		c2 = A[10] ^ kt;
		kt = A[22] | A[ 3];
		c3 = A[16] ^ kt;
		kt = A[ 3] & A[ 9];
		c4 = A[22] ^ kt;
		A[ 3] = c0;
		A[ 9] = c1;
		A[10] = c2;
		A[16] = c3;
		A[22] = c4;
		bnn = ~A[19];
		kt = A[ 7] | A[13];
		c0 = A[ 1] ^ kt;
		kt = A[13] & A[19];
		c1 = A[ 7] ^ kt;
		kt = bnn & A[20];
		c2 = A[13] ^ kt;
		kt = A[20] | A[ 1];
		c3 = bnn ^ kt;
		kt = A[ 1] & A[ 7];
		c4 = A[20] ^ kt;
		A[ 1] = c0;
		A[ 7] = c1;
		A[13] = c2;
		A[19] = c3;
		A[20] = c4;
		bnn = ~A[17];
		kt = A[ 5] & A[11];
		c0 = A[ 4] ^ kt;
		kt = A[11] | A[17];
		c1 = A[ 5] ^ kt;
		kt = bnn | A[23];
		c2 = A[11] ^ kt;
		kt = A[23] & A[ 4];
		c3 = bnn ^ kt;
		kt = A[ 4] | A[ 5];
		c4 = A[23] ^ kt;
		A[ 4] = c0;
		A[ 5] = c1;
		A[11] = c2;
		A[17] = c3;
		A[23] = c4;
		bnn = ~A[ 8];
		kt = bnn & A[14];
		c0 = A[ 2] ^ kt;
		kt = A[14] | A[15];
		c1 = bnn ^ kt;
		kt = A[15] & A[21];
		c2 = A[14] ^ kt;
		kt = A[21] | A[ 2];
		c3 = A[15] ^ kt;
		kt = A[ 2] & A[ 8];
		c4 = A[21] ^ kt;
		A[ 2] = c0;
		A[ 8] = c1;
		A[14] = c2;
		A[15] = c3;
		A[21] = c4;
		A[ 0] = A[ 0] ^ RC[j + 0];

		tt0 = A[ 6] ^ A[ 9];
		tt1 = A[ 7] ^ A[ 5];
		tt0 ^= A[ 8] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[24] ^ A[22];
		tt3 = A[20] ^ A[23];
		tt0 ^= A[21];
		tt2 ^= tt3;
		t0 = tt0 ^ tt2;

		tt0 = A[12] ^ A[10];
		tt1 = A[13] ^ A[11];
		tt0 ^= A[14] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[ 0] ^ A[ 3];
		tt3 = A[ 1] ^ A[ 4];
		tt0 ^= A[ 2];
		tt2 ^= tt3;
		t1 = tt0 ^ tt2;

		tt0 = A[18] ^ A[16];
		tt1 = A[19] ^ A[17];
		tt0 ^= A[15] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[ 6] ^ A[ 9];
		tt3 = A[ 7] ^ A[ 5];
		tt0 ^= A[ 8];
		tt2 ^= tt3;
		t2 = tt0 ^ tt2;

		tt0 = A[24] ^ A[22];
		tt1 = A[20] ^ A[23];
		tt0 ^= A[21] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[12] ^ A[10];
		tt3 = A[13] ^ A[11];
		tt0 ^= A[14];
		tt2 ^= tt3;
		t3 = tt0 ^ tt2;

		tt0 = A[ 0] ^ A[ 3];
		tt1 = A[ 1] ^ A[ 4];
		tt0 ^= A[ 2] ^ tt1;
		tt0 = (tt0 << 1) | (tt0 >> 63);
		tt2 = A[18] ^ A[16];
		tt3 = A[19] ^ A[17];
		tt0 ^= A[15];
		tt2 ^= tt3;
		t4 = tt0 ^ tt2;

		A[ 0] = A[ 0] ^ t0;
		A[ 3] = A[ 3] ^ t0;
		A[ 1] = A[ 1] ^ t0;
		A[ 4] = A[ 4] ^ t0;
		A[ 2] = A[ 2] ^ t0;
		A[ 6] = A[ 6] ^ t1;
		A[ 9] = A[ 9] ^ t1;
		A[ 7] = A[ 7] ^ t1;
		A[ 5] = A[ 5] ^ t1;
		A[ 8] = A[ 8] ^ t1;
		A[12] = A[12] ^ t2;
		A[10] = A[10] ^ t2;
		A[13] = A[13] ^ t2;
		A[11] = A[11] ^ t2;
		A[14] = A[14] ^ t2;
		A[18] = A[18] ^ t3;
		A[16] = A[16] ^ t3;
		A[19] = A[19] ^ t3;
		A[17] = A[17] ^ t3;
		A[15] = A[15] ^ t3;
		A[24] = A[24] ^ t4;
		A[22] = A[22] ^ t4;
		A[20] = A[20] ^ t4;
		A[23] = A[23] ^ t4;
		A[21] = A[21] ^ t4;
		A[ 3] = (A[ 3] << 36) | (A[ 3] >> (64 - 36));
		A[ 1] = (A[ 1] <<  3) | (A[ 1] >> (64 -  3));
		A[ 4] = (A[ 4] << 41) | (A[ 4] >> (64 - 41));
		A[ 2] = (A[ 2] << 18) | (A[ 2] >> (64 - 18));
		A[ 6] = (A[ 6] <<  1) | (A[ 6] >> (64 -  1));
		A[ 9] = (A[ 9] << 44) | (A[ 9] >> (64 - 44));
		A[ 7] = (A[ 7] << 10) | (A[ 7] >> (64 - 10));
		A[ 5] = (A[ 5] << 45) | (A[ 5] >> (64 - 45));
		A[ 8] = (A[ 8] <<  2) | (A[ 8] >> (64 - 2));
		A[12] = (A[12] << 62) | (A[12] >> (64 - 62));
		A[10] = (A[10] <<  6) | (A[10] >> (64 -  6));
		A[13] = (A[13] << 43) | (A[13] >> (64 - 43));
		A[11] = (A[11] << 15) | (A[11] >> (64 - 15));
		A[14] = (A[14] << 61) | (A[14] >> (64 - 61));
		A[18] = (A[18] << 28) | (A[18] >> (64 - 28));
		A[16] = (A[16] << 55) | (A[16] >> (64 - 55));
		A[19] = (A[19] << 25) | (A[19] >> (64 - 25));
		A[17] = (A[17] << 21) | (A[17] >> (64 - 21));
		A[15] = (A[15] << 56) | (A[15] >> (64 - 56));
		A[24] = (A[24] << 27) | (A[24] >> (64 - 27));
		A[22] = (A[22] << 20) | (A[22] >> (64 - 20));
		A[20] = (A[20] << 39) | (A[20] >> (64 - 39));
		A[23] = (A[23] <<  8) | (A[23] >> (64 -  8));
		A[21] = (A[21] << 14) | (A[21] >> (64 - 14));

		bnn = ~A[13];
		kt = A[ 9] | A[13];
		c0 = A[ 0] ^ kt;
		kt = bnn | A[17];
		c1 = A[ 9] ^ kt;
		kt = A[17] & A[21];
		c2 = A[13] ^ kt;
		kt = A[21] | A[ 0];
		c3 = A[17] ^ kt;
		kt = A[ 0] & A[ 9];
		c4 = A[21] ^ kt;
		A[ 0] = c0;
		A[ 9] = c1;
		A[13] = c2;
		A[17] = c3;
		A[21] = c4;
		bnn = ~A[14];
		kt = A[22] | A[ 1];
		c0 = A[18] ^ kt;
		kt = A[ 1] & A[ 5];
		c1 = A[22] ^ kt;
		kt = A[ 5] | bnn;
		c2 = A[ 1] ^ kt;
		kt = A[14] | A[18];
		c3 = A[ 5] ^ kt;
		kt = A[18] & A[22];
		c4 = A[14] ^ kt;
		A[18] = c0;
		A[22] = c1;
		A[ 1] = c2;
		A[ 5] = c3;
		A[14] = c4;
		bnn = ~A[23];
		kt = A[10] | A[19];
		c0 = A[ 6] ^ kt;
		kt = A[19] & A[23];
		c1 = A[10] ^ kt;
		kt = bnn & A[ 2];
		c2 = A[19] ^ kt;
		kt = A[ 2] | A[ 6];
		c3 = bnn ^ kt;
		kt = A[ 6] & A[10];
		c4 = A[ 2] ^ kt;
		A[ 6] = c0;
		A[10] = c1;
		A[19] = c2;
		A[23] = c3;
		A[ 2] = c4;
		bnn = ~A[11];
		kt = A[ 3] & A[ 7];
		c0 = A[24] ^ kt;
		kt = A[ 7] | A[11];
		c1 = A[ 3] ^ kt;
		kt = bnn | A[15];
		c2 = A[ 7] ^ kt;
		kt = A[15] & A[24];
		c3 = bnn ^ kt;
		kt = A[24] | A[ 3];
		c4 = A[15] ^ kt;
		A[24] = c0;
		A[ 3] = c1;
		A[ 7] = c2;
		A[11] = c3;
		A[15] = c4;
		bnn = ~A[16];
		kt = bnn & A[20];
		c0 = A[12] ^ kt;
		kt = A[20] | A[ 4];
		c1 = bnn ^ kt;
		kt = A[ 4] & A[ 8];
		c2 = A[20] ^ kt;
		kt = A[ 8] | A[12];
		c3 = A[ 4] ^ kt;
		kt = A[12] & A[16];
		c4 = A[ 8] ^ kt;
		A[12] = c0;
		A[16] = c1;
		A[20] = c2;
		A[ 4] = c3;
		A[ 8] = c4;
		A[ 0] = A[ 0] ^ RC[j + 1];
		t = A[ 5];
		A[ 5] = A[18];
		A[18] = A[11];
		A[11] = A[10];
		A[10] = A[ 6];
		A[ 6] = A[22];
		A[22] = A[20];
		A[20] = A[12];
		A[12] = A[19];
		A[19] = A[15];
		A[15] = A[24];
		A[24] = A[ 8];
		A[ 8] = t;
		t = A[ 1];
		A[ 1] = A[ 9];
		A[ 9] = A[14];
		A[14] = A[ 2];
		A[ 2] = A[13];
		A[13] = A[23];
		A[23] = A[ 4];
		A[ 4] = A[21];
		A[21] = A[16];
		A[16] = A[ 3];
		A[ 3] = A[17];
		A[17] = A[ 7];
		A[ 7] = t;
	}

	/*
	 * Invert some words back to normal representation.
	 */
	A[ 1] = ~A[ 1];
	A[ 2] = ~A[ 2];
	A[ 8] = ~A[ 8];
	A[12] = ~A[12];
	A[17] = ~A[17];
	A[20] = ~A[20];
}

#endif  // yyyASM_CORTEXM4-

/* see inner.h */
void
Zf(i_shake256_init)(inner_shake256_context *sc)
{
	sc->dptr = 0;

	/*
	 * Representation of an all-ones uint64_t is the same regardless
	 * of local endianness.
	 */
	memset(sc->st.A, 0, sizeof sc->st.A);
}

/* see inner.h */
void
Zf(i_shake256_inject)(inner_shake256_context *sc, const uint8_t *in, size_t len)
{
	size_t dptr;

	dptr = (size_t)sc->dptr;
	while (len > 0) {
		size_t clen, u;

		clen = 136 - dptr;
		if (clen > len) {
			clen = len;
		}
#if FALCON_LE  // yyyLE+1
		for (u = 0; u < clen; u ++) {
			sc->st.dbuf[dptr + u] ^= in[u];
		}
#else  // yyyLE+0
		for (u = 0; u < clen; u ++) {
			size_t v;

			v = u + dptr;
			sc->st.A[v >> 3] ^= (uint64_t)in[u] << ((v & 7) << 3);
		}
#endif  // yyyLE-
		dptr += clen;
		in += clen;
		len -= clen;
		if (dptr == 136) {
			process_block(sc->st.A);
			dptr = 0;
		}
	}
	sc->dptr = dptr;
}

/* see falcon.h */
void
Zf(i_shake256_flip)(inner_shake256_context *sc)
{
	/*
	 * We apply padding and pre-XOR the value into the state. We
	 * set dptr to the end of the buffer, so that first call to
	 * shake_extract() will process the block.
	 */
#if FALCON_LE  // yyyLE+1
	sc->st.dbuf[sc->dptr] ^= 0x1F;
	sc->st.dbuf[135] ^= 0x80;
#else  // yyyLE+0
	unsigned v;

	v = sc->dptr;
	sc->st.A[v >> 3] ^= (uint64_t)0x1F << ((v & 7) << 3);
	sc->st.A[16] ^= (uint64_t)0x80 << 56;
#endif  // yyyLE-
	sc->dptr = 136;
}

/* see falcon.h */
void
Zf(i_shake256_extract)(inner_shake256_context *sc, uint8_t *out, size_t len)
{
	size_t dptr;

	dptr = (size_t)sc->dptr;
	while (len > 0) {
		size_t clen;

		if (dptr == 136) {
			process_block(sc->st.A);
			dptr = 0;
		}
		clen = 136 - dptr;
		if (clen > len) {
			clen = len;
		}
		len -= clen;
#if FALCON_LE  // yyyLE+1
		memcpy(out, sc->st.dbuf + dptr, clen);
		dptr += clen;
		out += clen;
#else  // yyyLE+0
		while (clen -- > 0) {
			*out ++ = sc->st.A[dptr >> 3] >> ((dptr & 7) << 3);
			dptr ++;
		}
#endif  // yyyLE-
	}
	sc->dptr = dptr;
}
