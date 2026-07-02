/* SPDX-License-Identifier: GPL-2.0+ */
/*
 * Copyright (c) 2015 Google, Inc
 */

#ifndef __ALIGNMEM_H
#define __ALIGNMEM_H

/*
 * ARCH_DMA_MINALIGN is defined in asm/cache.h for each architecture.  It
 * is used to align DMA buffers.
 */
#ifndef __ASSEMBLY__
// #include <linux/kernel.h>
#include "cache.h"
#include <malloc.h>

/*
 * The ALLOC_CACHE_ALIGN_BUFFER macro is used to allocate a buffer on the
 * stack that meets the minimum architecture alignment requirements for DMA.
 * Such a buffer is useful for DMA operations where flushing and invalidating
 * the cache before and after a read and/or write operation is required for
 * correct operations.
 *
 * When called the macro creates an array on the stack that is sized such
 * that:
 *
 * 1) The beginning of the array can be advanced enough to be aligned.
 *
 * 2) The size of the aligned portion of the array is a multiple of the minimum
 *    architecture alignment required for DMA.
 *
 * 3) The aligned portion contains enough space for the original number of
 *    elements requested.
 *
 * The macro then creates a pointer to the aligned portion of this array and
 * assigns to the pointer the address of the first element in the aligned
 * portion of the array.
 *
 * Calling the macro as:
 *
 *     ALLOC_CACHE_ALIGN_BUFFER(uint32_t, buffer, 1024);
 *
 * Will result in something similar to saying:
 *
 *     uint32_t    buffer[1024];
 *
 * The following differences exist:
 *
 * 1) The resulting buffer is guaranteed to be aligned to the value of
 *    ARCH_DMA_MINALIGN.
 *
 * 2) The buffer variable created by the macro is a pointer to the specified
 *    type, and NOT an array of the specified type.  This can be very important
 *    if you want the address of the buffer, which you probably do, to pass it
 *    to the DMA hardware.  The value of &buffer is different in the two cases.
 *    In the macro case it will be the address of the pointer, not the address
 *    of the space reserved for the buffer.  However, in the second case it
 *    would be the address of the buffer.  So if you are replacing hard coded
 *    stack buffers with this macro you need to make sure you remove the & from
 *    the locations where you are taking the address of the buffer.
 *
 * Note that the size parameter is the number of array elements to allocate,
 * not the number of bytes.
 *
 * This macro can not be used outside of function scope, or for the creation
 * of a function scoped static buffer.  It can not be used to create a cache
 * line aligned global buffer.
 */
#define ALIGN(x,a)		__ALIGN_MASK((x),(typeof(x))(a)-1)
#define ALIGN_DOWN(x, a)	ALIGN((x) - ((a) - 1), (a))
#define __ALIGN_MASK(x,mask)	(((x)+(mask))&~(mask))
#define PTR_ALIGN(p, a)		((typeof(p))ALIGN((unsigned long)(p), (a)))
#define IS_ALIGNED(x, a)		(((x) & ((typeof(x))(a) - 1)) == 0)

#define __round_mask(x, y) ((__typeof__(x))((y)-1))
#define round_up(x, y) ((((x)-1) | __round_mask(x, y))+1)
#define round_down(x, y) ((x) & ~__round_mask(x, y))

#define FIELD_SIZEOF(t, f) (sizeof(((t*)0)->f))
#define DIV_ROUND_UP(n,d) (((n) + (d) - 1) / (d))

#define DIV_ROUND_DOWN_ULL(ll, d) \
	({ unsigned long long _tmp = (ll); do_div(_tmp, d); _tmp; })

#define DIV_ROUND_UP_ULL(ll, d)		DIV_ROUND_DOWN_ULL((ll) + (d) - 1, (d))

#define ROUND(a, b)		(((a) + (b) - 1) & ~((b) - 1))

#if BITS_PER_LONG == 32
# define DIV_ROUND_UP_SECTOR_T(ll,d) DIV_ROUND_UP_ULL(ll, d)
#else
# define DIV_ROUND_UP_SECTOR_T(ll,d) DIV_ROUND_UP(ll,d)
#endif

/* The `const' in roundup() prevents gcc-3.3 from calling __divdi3 */
#define roundup(x, y) (					\
{							\
	const typeof(y) __y = y;			\
	(((x) + (__y - 1)) / __y) * __y;		\
}							\
)
#define rounddown(x, y) (				\
{							\
	typeof(x) __x = (x);				\
	__x - (__x % (y));				\
}							\
)

#define ARRAY_SIZE(x) (sizeof(x) / sizeof((x)[0]))
#define PAD_COUNT(s, pad) (((s) - 1) / (pad) + 1)
#define PAD_SIZE(s, pad) (PAD_COUNT(s, pad) * pad)
#define ALLOC_ALIGN_BUFFER_PAD(type, name, size, align, pad)		\
	char __##name[ROUND(PAD_SIZE((size) * sizeof(type), pad), align)  \
		      + (align - 1)];					\
									\
	type *name = (type *)ALIGN((uintptr_t)__##name, align)
#define ALLOC_ALIGN_BUFFER(type, name, size, align)		\
	ALLOC_ALIGN_BUFFER_PAD(type, name, size, align, 1)
#define ALLOC_CACHE_ALIGN_BUFFER_PAD(type, name, size, pad)		\
	ALLOC_ALIGN_BUFFER_PAD(type, name, size, ARCH_DMA_MINALIGN, pad)
#define ALLOC_CACHE_ALIGN_BUFFER(type, name, size)			\
	ALLOC_ALIGN_BUFFER(type, name, size, ARCH_DMA_MINALIGN)

/*
 * DEFINE_CACHE_ALIGN_BUFFER() is similar to ALLOC_CACHE_ALIGN_BUFFER, but it's
 * purpose is to allow allocating aligned buffers outside of function scope.
 * Usage of this macro shall be avoided or used with extreme care!
 */
#define DEFINE_ALIGN_BUFFER(type, name, size, align)			\
	static char __##name[ALIGN(size * sizeof(type), align)]	\
			__aligned(align);				\
									\
	static type *name = (type *)__##name
#define DEFINE_CACHE_ALIGN_BUFFER(type, name, size)			\
	DEFINE_ALIGN_BUFFER(type, name, size, ARCH_DMA_MINALIGN)

/**
 * malloc_cache_aligned() - allocate a memory region aligned to cache line size
 *
 * This allocates memory at a cache-line boundary. The amount allocated may
 * be larger than requested as it is rounded up to the nearest multiple of the
 * cache-line size. This ensured that subsequent cache operations on this
 * memory (flush, invalidate) will not affect subsequently allocated regions.
 *
 * @size:	Minimum number of bytes to allocate
 *
 * Return: pointer to new memory region, or NULL if there is no more memory
 * available.
 */
static inline void *malloc_cache_aligned(size_t size)
{
	return memalign(ARCH_DMA_MINALIGN, ALIGN(size, ARCH_DMA_MINALIGN));
}
#endif

#endif /* __ALIGNMEM_H */
