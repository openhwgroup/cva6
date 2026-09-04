#ifndef HMODE_PANIC_H
#define HMODE_PANIC_H

#include "util.h"

__attribute__((noreturn)) void panic(void);
__attribute__((noreturn)) void panic_vector(void);

#define __sync_load(a) __atomic_load_n(a, __ATOMIC_ACQUIRE)
#define __sync_store(a, val) __atomic_store_n(a, val, __ATOMIC_RELEASE)
#define __sync_compare_and_swap_n(a, old_val, new_val) __atomic_compare_exchange_n(a, old_val, new_val, 0, __ATOMIC_RELEASE, __ATOMIC_ACQUIRE)
#define __sync_fetch_and_add(a, inc) __atomic_fetch_add(a, inc, __ATOMIC_ACQUIRE)

void reset(void);
void exit(int); // defined in `../common/syscalls.c`

#endif //HMODE_PANIC_H
