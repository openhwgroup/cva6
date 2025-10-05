// See LICENSE for license details.

// Test of PMP functionality.

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"

volatile int trap_expected;

#define INLINE inline __attribute__((always_inline))

uintptr_t handle_trap(uintptr_t cause, uintptr_t epc, uintptr_t regs[32])
{
  if (cause == CAUSE_ILLEGAL_INSTRUCTION)
    exit(0); // no PMP support

  if (!trap_expected || cause != CAUSE_LOAD_ACCESS)
    exit(1);
  trap_expected = 0;
  return epc + insn_len(epc);
}

#define SCRATCH RISCV_PGSIZE
uintptr_t scratch[RISCV_PGSIZE / sizeof(uintptr_t)] __attribute__((aligned(RISCV_PGSIZE)));
uintptr_t l1pt[RISCV_PGSIZE / sizeof(uintptr_t)] __attribute__((aligned(RISCV_PGSIZE)));
uintptr_t l2pt[RISCV_PGSIZE / sizeof(uintptr_t)] __attribute__((aligned(RISCV_PGSIZE)));
#if __riscv_xlen == 64
uintptr_t l3pt[RISCV_PGSIZE / sizeof(uintptr_t)] __attribute__((aligned(RISCV_PGSIZE)));
#else
#define l3pt l2pt
#endif

static void init_pt()
{
  l1pt[0] = ((uintptr_t)l2pt >> RISCV_PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
  l3pt[SCRATCH / RISCV_PGSIZE] = ((uintptr_t)scratch >> RISCV_PGSHIFT << PTE_PPN_SHIFT) | PTE_A | PTE_D | PTE_V | PTE_R | PTE_W;
#if __riscv_xlen == 64
  l2pt[0] = ((uintptr_t)l3pt >> RISCV_PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
  uintptr_t vm_choice = SATP_MODE_SV39;
#else
  uintptr_t vm_choice = SATP_MODE_SV32;
#endif
  write_csr(sptbr, ((uintptr_t)l1pt >> RISCV_PGSHIFT) |
                   (vm_choice * (SATP_MODE & ~(SATP_MODE<<1))));
  write_csr(pmpcfg0, (PMP_NAPOT | PMP_R) << 16);
  write_csr(pmpaddr2, -1);
}

INLINE uintptr_t va2pa(uintptr_t va)
{
  if (va < SCRATCH || va >= SCRATCH + RISCV_PGSIZE)
    exit(3);
  return va - SCRATCH + (uintptr_t)scratch;
}

#define GRANULE (1UL << PMP_SHIFT)

typedef struct {
  uintptr_t cfg;
  uintptr_t a0;
  uintptr_t a1;
} pmpcfg_t;

INLINE int pmp_ok(pmpcfg_t p, uintptr_t addr, uintptr_t size)
{
  if ((p.cfg & PMP_A) == 0)
    return 1;

  if ((p.cfg & PMP_A) != PMP_TOR) {
    uintptr_t range = 1;

    if ((p.cfg & PMP_A) == PMP_NAPOT) {
      range <<= 1;
      for (uintptr_t i = 1; i; i <<= 1) {
        if ((p.a1 & i) == 0)
          break;
        p.a1 &= ~i;
        range <<= 1;
      }
    }

    p.a0 = p.a1;
    p.a1 = p.a0 + range;
  }

  p.a0 *= GRANULE;
  p.a1 *= GRANULE;
  addr = va2pa(addr);

  uintptr_t hits = 0;
  for (uintptr_t i = 0; i < size; i += GRANULE) {
    if (p.a0 <= addr + i && addr + i < p.a1)
      hits += GRANULE;
  }

  return hits == 0 || hits >= size;
}

INLINE void test_one(uintptr_t addr, uintptr_t size)
{
  uintptr_t new_mstatus = (read_csr(mstatus) & ~MSTATUS_MPP) | (MSTATUS_MPP & (MSTATUS_MPP >> 1)) | MSTATUS_MPRV;
  switch (size) {
    case 1: asm volatile ("csrrw %0, mstatus, %0; lb x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
    case 2: asm volatile ("csrrw %0, mstatus, %0; lh x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
    case 4: asm volatile ("csrrw %0, mstatus, %0; lw x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
#if __riscv_xlen >= 64
    case 8: asm volatile ("csrrw %0, mstatus, %0; ld x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
#endif
    default: __builtin_unreachable();
  }
}

INLINE void test_all_sizes(pmpcfg_t p, uintptr_t addr)
{
  for (size_t size = 1; size <= sizeof(uintptr_t); size *= 2) {
    if (addr & (size - 1))
      continue;
    trap_expected = !pmp_ok(p, addr, size);
    test_one(addr, size);
    if (trap_expected)
      exit(2);
  }
}

INLINE void test_range_once(pmpcfg_t p, uintptr_t base, uintptr_t range)
{
  for (uintptr_t addr = base; addr < base + range; addr += GRANULE)
    test_all_sizes(p, addr);
}

INLINE pmpcfg_t set_pmp(pmpcfg_t p)
{
  uintptr_t cfg0 = read_csr(pmpcfg0);
  write_csr(pmpcfg0, cfg0 & ~0xff00);
  write_csr(pmpaddr0, p.a0);
  write_csr(pmpaddr1, p.a1);
  write_csr(pmpcfg0, ((p.cfg << 8) & 0xff00) | (cfg0 & ~0xff00));
  asm volatile ("sfence.vma" ::: "memory");
  return p;
}

INLINE pmpcfg_t set_pmp_range(uintptr_t base, uintptr_t range)
{
  pmpcfg_t p;
  p.cfg = PMP_TOR | PMP_R;
  p.a0 = base >> PMP_SHIFT;
  p.a1 = (base + range) >> PMP_SHIFT;
  return set_pmp(p);
}

INLINE pmpcfg_t set_pmp_napot(uintptr_t base, uintptr_t range)
{
  pmpcfg_t p;
  p.cfg = PMP_R | (range > GRANULE ? PMP_NAPOT : PMP_NA4);
  p.a0 = 0;
  p.a1 = (base + (range/2 - 1)) >> PMP_SHIFT;
  return set_pmp(p);
}

static void test_range(uintptr_t addr, uintptr_t range)
{
  pmpcfg_t p = set_pmp_range(va2pa(addr), range);
  test_range_once(p, addr, range);

  if ((range & (range - 1)) == 0 && (addr & (range - 1)) == 0) {
    p = set_pmp_napot(va2pa(addr), range);
    test_range_once(p, addr, range);
  }
}

static void test_ranges(uintptr_t addr, uintptr_t size)
{
  for (uintptr_t range = GRANULE; range <= size; range += GRANULE)
    test_range(addr, range);
}

static void exhaustive_test(uintptr_t addr, uintptr_t size)
{
  for (uintptr_t base = addr; base < addr + size; base += GRANULE)
    test_ranges(base, size - (base - addr));
}

int main()
{
  init_pt();

  const int max_exhaustive = 32;
  exhaustive_test(SCRATCH, max_exhaustive);
  exhaustive_test(SCRATCH + RISCV_PGSIZE - max_exhaustive, max_exhaustive);

  test_range(SCRATCH, RISCV_PGSIZE);
  test_range(SCRATCH, RISCV_PGSIZE / 2);
  test_range(SCRATCH + RISCV_PGSIZE / 2, RISCV_PGSIZE / 2);

  return 0;
}
