/*
 * RISCV CPU emulator
 *
 * Copyright (c) 2016-2017 Fabrice Bellard
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

#include "dromajo.h"
#include <stdlib.h>
#include <stdarg.h>
#include <stdbool.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>
#include <fcntl.h>
#include <unistd.h>
#include <err.h>
#include <fstream>
#include <iomanip>

#include "cutils.h"
#include "iomem.h"
#include "riscv_machine.h"
#include "LiveCacheCore.h"

// NOTE: Use GET_INSN_COUNTER not mcycle because this is just to track advancement of simulation
#define write_reg(x, val) ({s->most_recently_written_reg = (x); \
                           s->reg_prior[x] = s->reg[x]; \
                           s->reg[x] = (val);})
#define read_reg(x)       (s->reg[x])

#define write_fp_reg(x, val) ({s->most_recently_written_fp_reg = (x); \
                               s->fp_reg[x] = (val);                  \
                               s->fs = 3;})
#define read_fp_reg(x)       (s->fp_reg[x])

/*
 * Boom/Rocket doesn't implement all bits in all CSRs but
 * stores Sv+1, that, is 49 bits and reads are sign-extended from bit
 * 49 onwards.  For the emulator we achieve this by keeping the
 * register canonical on writes (as opposed to reads).
 */
#define CANONICAL_S49(v) ((intptr_t)(v) << (63-48) >> (63-48))
#define MEPC_TRUNCATE   CANONICAL_S49
#define MTVAL_TRUNCATE  CANONICAL_S49
#define SEPC_TRUNCATE   CANONICAL_S49
#define STVAL_TRUNCATE  CANONICAL_S49

// PMPADDR CSRs only have 38-bits
#define PMPADDR_MASK	0x3fffffffff

#ifdef CONFIG_LOGFILE
static FILE *log_file;

void log_vprintf(const char *fmt, va_list ap)
{
    if (!log_file)
        log_file = fopen("/tmp/riscemu.log", "wb");
    vfprintf(log_file, fmt, ap);
}
#else
void log_vprintf(const char *fmt, va_list ap)
{
    vprintf(fmt, ap);
}
#endif

void __attribute__((format(printf, 1, 2))) log_printf(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    log_vprintf(fmt, ap);
    va_end(ap);
}

static void fprint_target_ulong(FILE *f, target_ulong a)
{
    fprintf(f, "%" PR_target_ulong, a);
}

static void print_target_ulong(target_ulong a)
{
    fprint_target_ulong(dromajo_stderr, a);
}

static const char *reg_name[32] = {
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
    "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
    "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
    "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"
};

static target_ulong get_mstatus(RISCVCPUState *s, target_ulong mask);
static void dump_regs(RISCVCPUState *s)
{
    int i, cols;
    const char *priv_str = "USHM";
    cols = 256 / 64;
    fprintf(dromajo_stderr, "pc =");
    print_target_ulong(s->pc);
    fprintf(dromajo_stderr, " ");
    for (i = 1; i < 32; i++) {
        fprintf(dromajo_stderr, "%-3s=", reg_name[i]);
        print_target_ulong(s->reg[i]);
        if ((i & (cols - 1)) == (cols - 1))
            fprintf(dromajo_stderr, "\n");
        else
            fprintf(dromajo_stderr, " ");
    }
    fprintf(dromajo_stderr, "priv=%c", priv_str[s->priv]);
    fprintf(dromajo_stderr, " mstatus=");
    print_target_ulong(get_mstatus(s, (target_ulong)-1));
    fprintf(dromajo_stderr, " insn_counter=%" PRId64, s->insn_counter);
    fprintf(dromajo_stderr, " minstret=%" PRId64, s->minstret);
    fprintf(dromajo_stderr, " mcycle=%" PRId64, s->mcycle);
    fprintf(dromajo_stderr, "\n");
#if 1
    fprintf(dromajo_stderr, " mideleg=");
    print_target_ulong(s->mideleg);
    fprintf(dromajo_stderr, " mie=");
    print_target_ulong(s->mie);
    fprintf(dromajo_stderr, " mip=");
    print_target_ulong(s->mip);
    fprintf(dromajo_stderr, "\n");
#endif
}

static inline void track_write(RISCVCPUState *s, uint64_t vaddr, uint64_t paddr, uint64_t data, int size) {
#ifdef LIVECACHE
    s->machine->llc->write(paddr);
#endif
}

static inline uint64_t track_dread(RISCVCPUState *s, uint64_t vaddr, uint64_t paddr, uint64_t data, int size) {
#ifdef LIVECACHE
  s->machine->llc->read(paddr);
#endif

  return data;
}

static inline uint64_t track_iread(RISCVCPUState *s, uint64_t vaddr, uint64_t paddr, uint64_t data, int size) {
#ifdef LIVECACHE
  s->machine->llc->read(paddr);
#endif
  assert(size == 16 || size == 32);

  return data;
}

/* "PMP checks are applied to all accesses when the hart is running in
 * S or U modes, and for loads and stores when the MPRV bit is set in
 * the mstatus register and the MPP field in the mstatus register
 * contains S or U. Optionally, PMP checks may additionally apply to
 * M-mode accesses, in which case the PMP registers themselves are
 * locked, so that even M-mode software cannot change them without a
 * system reset.  In effect, PMP can grant permissions to S and U
 * modes, which by default have none, and can revoke permissions from
 * M-mode, which by default has full permissions." */
bool
riscv_cpu_pmp_access_ok(RISCVCPUState *s, uint64_t paddr, size_t size, pmpcfg_t perm)
{
    return true; //FIXME: HACK for Ariane
    int priv;

    /* rv64mi-p-access expects illegal physical addresses to fail. */
    if ((uint64_t)paddr >> s->physical_addr_len != 0)
        return false;

    if ((s->mstatus & MSTATUS_MPRV) && !(perm & PMPCFG_X)) {
        /* use previous privilege */
        priv = (s->mstatus >> MSTATUS_MPP_SHIFT) & 3;
    } else {
        priv = s->priv;
    }

    // Check for _any_ bytes from the range overlapping with a PMP
    // region (we don't support the cases where the PMP region is
    // smaller than the access).
    for (int i = 0; i < s->pmp_n; ++i)
        // [lo;hi) `intersect` [paddr;paddr+size) is non-empty
        if (s->pmp[i].lo <= paddr + size - 1 && paddr < s->pmp[i].hi)
            if (priv < PRV_M || s->pmpcfg[i] & PMPCFG_L)
                return (perm & s->pmpcfg[i]) == perm;
            else
                return true;

    return priv == PRV_M;
}

static inline PhysMemoryRange *
get_phys_mem_range_pmp(RISCVCPUState *s, uint64_t paddr, size_t size, pmpcfg_t perm)
{
    if (!riscv_cpu_pmp_access_ok(s, paddr, size, perm))
        return NULL;
    else
        return get_phys_mem_range(s->mem_map, paddr);
}

/* addr must be aligned. Only RAM accesses are supported */
#define PHYS_MEM_READ_WRITE(size, uint_type)                            \
    void riscv_phys_write_u ## size(RISCVCPUState *s, target_ulong paddr, \
                                    uint_type val, bool *fail)          \
    {                                                                   \
        PhysMemoryRange *pr = get_phys_mem_range_pmp(s, paddr, size/8, PMPCFG_W); \
        if (!pr || !pr->is_ram) {                                       \
            *fail = true;                                               \
            return;                                                     \
        }                                                               \
        track_write(s, paddr, paddr, val, size);                        \
        *(uint_type *)(pr->phys_mem + (uintptr_t)(paddr - pr->addr)) = val; \
        *fail = false;                                                  \
    }                                                                   \
                                                                        \
    uint_type riscv_phys_read_u ## size(RISCVCPUState *s, target_ulong paddr, \
                                        bool *fail)                     \
    {                                                                   \
        PhysMemoryRange *pr = get_phys_mem_range_pmp(s, paddr, size/8, PMPCFG_R); \
        if (!pr) {                                                      \
            *fail = true;                                               \
            return 0;                                                   \
        }                                                               \
        uint_type pval = *(uint_type *)(pr->phys_mem +                  \
                                        (uintptr_t)(paddr - pr->addr)); \
        pval = track_dread(s, paddr, paddr, pval, size);                \
        *fail = false;                                                  \
        return pval;                                                    \
    }

PHYS_MEM_READ_WRITE(8, uint8_t)
PHYS_MEM_READ_WRITE(32, uint32_t)
PHYS_MEM_READ_WRITE(64, uint64_t)

/* return 0 if OK, != 0 if exception */
#define TARGET_READ_WRITE(size, uint_type, size_log2)                   \
    static inline __exception int target_read_u ## size(RISCVCPUState *s, uint_type *pval, target_ulong addr) \
    {                                                                   \
        uint32_t tlb_idx;                                               \
        if (!CONFIG_ALLOW_MISALIGNED_ACCESS && (addr & (size/8 - 1)) != 0) { \
            s->pending_tval = addr;                                     \
            s->pending_exception = CAUSE_MISALIGNED_LOAD;               \
            return -1;                                                  \
        }                                                               \
        tlb_idx = (addr >> PG_SHIFT) & (TLB_SIZE - 1);                  \
        if (likely(s->tlb_read[tlb_idx].vaddr == (addr & ~(PG_MASK & ~((size / 8) - 1))))) { \
            uint64_t data = *(uint_type *)(s->tlb_read[tlb_idx].mem_addend + (uintptr_t)addr); \
            uint64_t paddr = s->tlb_read_paddr_addend[tlb_idx] + addr;  \
            *pval = track_dread(s, addr, paddr, data, size);            \
            return 0;                                                   \
        }                                                               \
                                                                        \
        mem_uint_t val;                                                 \
        int ret = riscv_cpu_read_memory(s, &val, addr, size_log2);      \
        if (ret)                                                        \
            return ret;                                                 \
        *pval = val;                                                    \
        return 0;                                                       \
    }                                                                   \
                                                                        \
    static inline __exception int target_write_u ## size(RISCVCPUState *s, target_ulong addr, uint_type val) \
    {                                                                   \
        uint32_t tlb_idx;                                               \
        if (!CONFIG_ALLOW_MISALIGNED_ACCESS && (addr & (size/8 - 1)) != 0) { \
            s->pending_tval = addr;                                     \
            s->pending_exception = CAUSE_MISALIGNED_STORE;              \
            return -1;                                                  \
        }                                                               \
        tlb_idx = (addr >> PG_SHIFT) & (TLB_SIZE - 1);                  \
        if (likely(s->tlb_write[tlb_idx].vaddr == (addr & ~(PG_MASK & ~((size / 8) - 1))))) { \
            *(uint_type *)(s->tlb_write[tlb_idx].mem_addend + (uintptr_t)addr) = val; \
            uint64_t paddr = s->tlb_write_paddr_addend[tlb_idx] + addr;  \
            track_write(s, addr, paddr, val, size);                     \
            return 0;                                                   \
        }                                                               \
                                                                        \
        return riscv_cpu_write_memory(s, addr, val, size_log2);         \
    }

TARGET_READ_WRITE(8, uint8_t, 0)
TARGET_READ_WRITE(16, uint16_t, 1)
TARGET_READ_WRITE(32, uint32_t, 2)
#if MLEN >= 64
TARGET_READ_WRITE(64, uint64_t, 3)
#endif
#if MLEN >= 128
TARGET_READ_WRITE(128, uint128_t, 4)
#endif

#define PTE_V_MASK (1 << 0)
#define PTE_U_MASK (1 << 4)
#define PTE_A_MASK (1 << 6)
#define PTE_D_MASK (1 << 7)

/* access = 0: read, 1 = write, 2 = code. Set the exception_pending
   field if necessary. return 0 if OK, -1 if translation error, -2 if
   the physical address is illegal. */
int riscv_cpu_get_phys_addr(RISCVCPUState *s,
                            target_ulong vaddr,
                            riscv_memory_access_t access,
                            target_ulong *ppaddr)
{
    int mode, levels, pte_bits, pte_idx, pte_mask, pte_size_log2, xwr, priv;
    int need_write, vaddr_shift, i, pte_addr_bits;
    target_ulong pte_addr, pte, vaddr_mask, paddr;

    if ((s->mstatus & MSTATUS_MPRV) && access != ACCESS_CODE) {
        /* use previous privilege */
        priv = (s->mstatus >> MSTATUS_MPP_SHIFT) & 3;
    } else {
        priv = s->priv;
    }

    if (priv == PRV_M) {
        *ppaddr = vaddr;
        return 0;
    }
    mode = (s->satp >> 60) & 0xf;
    if (mode == 0) {
        /* bare: no translation */
        *ppaddr = vaddr;
        return 0;
    } else {
        /* sv39/sv48 */
        levels = mode - 8 + 3;
        pte_size_log2 = 3;
        vaddr_shift = 64 - (PG_SHIFT + levels * 9);
        if ((((target_long)vaddr << vaddr_shift) >> vaddr_shift) != (target_long)vaddr)
            return -1;
        pte_addr_bits = 44;
    }
    pte_addr = (s->satp & (((target_ulong)1 << pte_addr_bits) - 1)) << PG_SHIFT;
    pte_bits = 12 - pte_size_log2;
    pte_mask = (1 << pte_bits) - 1;
    for (i = 0; i < levels; i++) {
        bool fail;

        vaddr_shift = PG_SHIFT + pte_bits * (levels - 1 - i);
        pte_idx = (vaddr >> vaddr_shift) & pte_mask;
        pte_addr += pte_idx << pte_size_log2;
        if (pte_size_log2 == 2)
            pte = riscv_phys_read_u32(s, pte_addr, &fail);
        else
            pte = riscv_phys_read_u64(s, pte_addr, &fail);

        if (fail)
            return -2;

        if (!(pte & PTE_V_MASK))
            return -1; /* invalid PTE */

        paddr = (pte >> 10) << PG_SHIFT;
        xwr = (pte >> 1) & 7;
        if (xwr != 0) {
            if (xwr == 2 || xwr == 6)
                return -1;

            /* priviledge check */
            if (priv == PRV_S) {
                if ((pte & PTE_U_MASK) && !(s->mstatus & MSTATUS_SUM))
                    return -1;
            } else {
                if (!(pte & PTE_U_MASK))
                    return -1;
            }
            /* protection check */
            /* MXR allows read access to execute-only pages */
            if (s->mstatus & MSTATUS_MXR)
                xwr |= (xwr >> 2);

            if (((xwr >> access) & 1) == 0)
                return -1;

            /* 6. Check for misaligned superpages */
            unsigned ppn = pte >> 10;
            int j = levels-1 - i;
            if (((1 << j) - 1) & ppn)
                return -1;

            /*
              RISC-V Priv. Spec 1.11 (draft) Section 4.3.1 offers two
              ways to handle the A and D TLB flags.  Spike uses the
              software managed approach whereas DROMAJO used to manage
              them (causing far fewer exceptions).
            */
            if (CONFIG_SW_MANAGED_A_AND_D) {
                if (!(pte & PTE_A_MASK))
                    return -1; // Must have A on access

                if (access == ACCESS_WRITE && !(pte & PTE_D_MASK))
                    return -1; // Must have D on write
            } else {
                need_write = !(pte & PTE_A_MASK) ||
                    (!(pte & PTE_D_MASK) && access == ACCESS_WRITE);
                pte |= PTE_A_MASK;
                if (access == ACCESS_WRITE)
                    pte |= PTE_D_MASK;
                if (need_write) {
                    bool fail;
                    if (pte_size_log2 == 2)
                        riscv_phys_write_u32(s, pte_addr, pte, &fail);
                    else
                        riscv_phys_write_u64(s, pte_addr, pte, &fail);
                    if (fail)
                        return -2;
                }
            }

            vaddr_mask = ((target_ulong)1 << vaddr_shift) - 1;
            *ppaddr = paddr & ~vaddr_mask | vaddr & vaddr_mask;
            return 0;
        }

        pte_addr = paddr;
    }

    return -1;
}

/* return 0 if OK, != 0 if exception */
no_inline int riscv_cpu_read_memory(RISCVCPUState *s, mem_uint_t *pval,
                                    target_ulong addr, int size_log2)
{
    int size, tlb_idx, err, al;
    target_ulong paddr, offset;
    uint8_t *ptr;
    PhysMemoryRange *pr;
    mem_uint_t ret;

    /* first handle unaligned accesses */
    size = 1 << size_log2;
    al = addr & (size - 1);
    if (!CONFIG_ALLOW_MISALIGNED_ACCESS && al != 0) {
        s->pending_tval = addr;
        s->pending_exception = CAUSE_MISALIGNED_LOAD;
        return -1;
    }

    if (al != 0) {
        switch (size_log2) {
        case 1:
            {
                uint8_t v0, v1;
                err = target_read_u8(s, &v0, addr);
                if (err)
                    return err;
                err = target_read_u8(s, &v1, addr + 1);
                if (err)
                    return err;
                ret = v0 | (v1 << 8);
            }
            break;
        case 2:
            {
                uint32_t v0, v1;
                addr -= al;
                err = target_read_u32(s, &v0, addr);
                if (err)
                    return err;
                err = target_read_u32(s, &v1, addr + 4);
                if (err)
                    return err;
                ret = (v0 >> (al * 8)) | (v1 << (32 - al * 8));
            }
            break;
#if MLEN >= 64
        case 3:
            {
                uint64_t v0, v1;
                addr -= al;
                err = target_read_u64(s, &v0, addr);
                if (err)
                    return err;
                err = target_read_u64(s, &v1, addr + 8);
                if (err)
                    return err;
                ret = (v0 >> (al * 8)) | (v1 << (64 - al * 8));
            }
            break;
#endif
#if MLEN >= 128
        case 4:
            {
                uint128_t v0, v1;
                addr -= al;
                err = target_read_u128(s, &v0, addr);
                if (err)
                    return err;
                err = target_read_u128(s, &v1, addr + 16);
                if (err)
                    return err;
                ret = (v0 >> (al * 8)) | (v1 << (128 - al * 8));
            }
            break;
#endif
        default:
            abort();
        }
        paddr = addr; // No translation for this request
    } else {
        int err = riscv_cpu_get_phys_addr(s, addr, ACCESS_READ, &paddr);

        if (err) {
            s->pending_tval = addr;
            s->pending_exception = err == -1
                ? CAUSE_LOAD_PAGE_FAULT : CAUSE_FAULT_LOAD;
            return -1;
        }
        pr = get_phys_mem_range_pmp(s, paddr, size, PMPCFG_R);
        if (!pr) {
#ifdef DUMP_INVALID_MEM_ACCESS
            fprintf(dromajo_stderr, "riscv_cpu_read_memory: invalid physical address 0x");
            print_target_ulong(paddr);
            fprintf(dromajo_stderr, "\n");
#endif
            s->pending_tval = addr;
            s->pending_exception = CAUSE_FAULT_LOAD;
            return -1;
        }

        if (pr->is_ram) {
            tlb_idx = (addr >> PG_SHIFT) & (TLB_SIZE - 1);
            ptr = pr->phys_mem + (uintptr_t)(paddr - pr->addr);
            s->tlb_read[tlb_idx].vaddr        = addr & ~PG_MASK;
#ifdef PADDR_INLINE
            s->tlb_read[tlb_idx].paddr_addend = paddr - addr;
#else
            s->tlb_read_paddr_addend[tlb_idx] = paddr - addr;
#endif
            s->tlb_read[tlb_idx].mem_addend   = (uintptr_t)ptr - addr;
            switch (size_log2) {
            case 0:
                ret = *(uint8_t *)ptr;
                break;
            case 1:
                ret = *(uint16_t *)ptr;
                break;
            case 2:
                ret = *(uint32_t *)ptr;
                break;
#if MLEN >= 64
            case 3:
                ret = *(uint64_t *)ptr;
                break;
#endif
#if MLEN >= 128
            case 4:
                ret = *(uint128_t *)ptr;
                break;
#endif
            default:
                abort();
            }
        } else {
            offset = paddr - pr->addr;
            if (((pr->devio_flags >> size_log2) & 1) != 0) {
                ret = pr->read_func(pr->opaque, offset, size_log2);
            }
#if MLEN >= 64
            else if ((pr->devio_flags & DEVIO_SIZE32) && size_log2 == 3) {
                /* emulate 64 bit access */
                ret = pr->read_func(pr->opaque, offset, 2);
                ret |= (uint64_t)pr->read_func(pr->opaque, offset + 4, 2) << 32;
            }
#endif
            else {
#ifdef DUMP_INVALID_MEM_ACCESS
                fprintf(dromajo_stderr, "unsupported device read access: addr=0x");
                print_target_ulong(paddr);
                fprintf(dromajo_stderr, " width=%d bits\n", 1 << (3 + size_log2));
#endif
                ret = 0;
            }
        }
    }
    *pval = track_dread(s, addr, paddr, ret, size);
    return 0;
}

/* return 0 if OK, != 0 if exception */
no_inline int riscv_cpu_write_memory(RISCVCPUState *s, target_ulong addr,
                                mem_uint_t val, int size_log2)
{
    int size, i, tlb_idx, err;
    target_ulong paddr, offset;
    uint8_t *ptr;
    PhysMemoryRange *pr;

    /* first handle unaligned accesses */
    size = 1 << size_log2;
    if (!CONFIG_ALLOW_MISALIGNED_ACCESS && (addr & (size - 1)) != 0) {
        s->pending_tval = addr;
        s->pending_exception = CAUSE_MISALIGNED_STORE;
        return -1;
    } else if ((addr & (size - 1)) != 0) {
        for (i = 0; i < size; i++) {
            err = target_write_u8(s, addr + i, (val >> (8 * i)) & 0xff);
            if (err)
                return err;
        }
        paddr = addr;
    } else {
        int err = riscv_cpu_get_phys_addr(s, addr, ACCESS_WRITE, &paddr);

        if (err) {
            s->pending_tval = addr;
            s->pending_exception = err == -1 ?
                CAUSE_STORE_PAGE_FAULT : CAUSE_FAULT_STORE;
            return -1;
        }
        pr = get_phys_mem_range_pmp(s, paddr, size, PMPCFG_W);
        if (!pr) {
#ifdef DUMP_INVALID_MEM_ACCESS
            fprintf(dromajo_stderr, "riscv_cpu_write_memory: invalid physical address 0x");
            print_target_ulong(paddr);
            fprintf(dromajo_stderr, "\n");
#endif
            s->pending_tval = addr;
            s->pending_exception = CAUSE_FAULT_STORE;
            return -1;
        } else if (pr->is_ram) {
            phys_mem_set_dirty_bit(pr, paddr - pr->addr);
            tlb_idx = (addr >> PG_SHIFT) & (TLB_SIZE - 1);
            ptr = pr->phys_mem + (uintptr_t)(paddr - pr->addr);
            s->tlb_write[tlb_idx].vaddr        = addr & ~PG_MASK;
#ifdef PADDR_INLINE
            s->tlb_write[tlb_idx].paddr_addend = paddr - addr;
#else
            s->tlb_write_paddr_addend[tlb_idx] = paddr - addr;
#endif
            s->tlb_write[tlb_idx].mem_addend   = (uintptr_t)ptr - addr;
            switch (size_log2) {
            case 0:
                *(uint8_t *)ptr = val;
                break;
            case 1:
                *(uint16_t *)ptr = val;
                break;
            case 2:
                *(uint32_t *)ptr = val;
                break;
#if MLEN >= 64
            case 3:
                *(uint64_t *)ptr = val;
                break;
#endif
#if MLEN >= 128
            case 4:
                *(uint128_t *)ptr = val;
                break;
#endif
            default:
                abort();
            }
        } else {
            offset = paddr - pr->addr;
            if (((pr->devio_flags >> size_log2) & 1) != 0) {
                pr->write_func(pr->opaque, offset, val, size_log2);
            }
#if MLEN >= 64
            else if ((pr->devio_flags & DEVIO_SIZE32) && size_log2 == 3) {
                /* emulate 64 bit access */
                pr->write_func(pr->opaque, offset,
                               val & 0xffffffff, 2);
                pr->write_func(pr->opaque, offset + 4,
                               (val >> 32) & 0xffffffff, 2);
            }
#endif
            else {
#ifdef DUMP_INVALID_MEM_ACCESS
                fprintf(dromajo_stderr, "unsupported device write access: addr=0x");
                print_target_ulong(paddr);
                fprintf(dromajo_stderr, " width=%d bits\n", 1 << (3 + size_log2));
#endif
            }
        }
    }
    track_write(s, addr, paddr, val, size);
    return 0;
}

struct __attribute__((packed)) unaligned_u32 {
    uint32_t u32;
};

/* unaligned access at an address known to be a multiple of 2 */
static uint32_t get_insn32(uint8_t *ptr)
{
    return ((struct unaligned_u32 *)ptr)->u32;
}

/* return 0 if OK, != 0 if exception */
static no_inline __exception int target_read_insn_slow(RISCVCPUState *s,
                                                       uint32_t *insn,
                                                       int size,
                                                       target_ulong addr)
{
    int tlb_idx;
    target_ulong paddr;
    uint8_t *ptr;
    PhysMemoryRange *pr;

    int err = riscv_cpu_get_phys_addr(s, addr, ACCESS_CODE, &paddr);
    if (err) {
        s->pending_tval = addr;
        s->pending_exception = err == -1 ?
            CAUSE_FETCH_PAGE_FAULT : CAUSE_FAULT_FETCH;
        return -1;
    }
    pr = get_phys_mem_range_pmp(s, paddr, size/8, PMPCFG_X);
    if (!pr || !pr->is_ram) {
        /* We only allow execution from RAM */
        s->pending_tval = addr;
        s->pending_exception = CAUSE_FAULT_FETCH;
        return -1;
    }
    tlb_idx = (addr >> PG_SHIFT) & (TLB_SIZE - 1);
    ptr = pr->phys_mem + (uintptr_t)(paddr - pr->addr);
    if (riscv_cpu_pmp_access_ok(s, paddr & ~PG_MASK, PG_MASK + 1, PMPCFG_X)) {
        /* All of this page has full execute access so we can bypass
         * the slow PMP checks. */
        s->tlb_code[tlb_idx].vaddr        = addr & ~PG_MASK;
        s->tlb_code_paddr_addend[tlb_idx] = paddr - addr;
        s->tlb_code[tlb_idx].mem_addend   = (uintptr_t)ptr - addr;
    }

    /* check for page crossing */
    int tlb_idx_cross = ((addr+2) >> PG_SHIFT) & (TLB_SIZE - 1);
    if (tlb_idx != tlb_idx_cross && size == 32) {
        target_ulong paddr_cross;
        int err = riscv_cpu_get_phys_addr(s, addr+2, ACCESS_CODE, &paddr_cross);
        if (err) {
            s->pending_tval = addr;
            s->pending_exception = err == -1 ?
                CAUSE_FETCH_PAGE_FAULT : CAUSE_FAULT_FETCH;
            return -1;
        }

        PhysMemoryRange *pr_cross = get_phys_mem_range_pmp(s, paddr_cross, 2, PMPCFG_X);
        if (!pr_cross || !pr_cross->is_ram) {
            /* We only allow execution from RAM */
            s->pending_tval = addr;
            s->pending_exception = CAUSE_FAULT_FETCH;
            return -1;
        }
        uint8_t *ptr_cross = pr_cross->phys_mem + (uintptr_t)(paddr_cross - pr_cross->addr);

        uint32_t data1 = (uint32_t)*((uint16_t*)ptr);
        uint32_t data2 = (uint32_t)*((uint16_t*)ptr_cross);

        data1 = track_iread(s, addr, paddr,       data1, 16);
        data2 = track_iread(s, addr, paddr_cross, data2, 16);

        *insn = data1 | (data2 << 16);

        return 0;
    }

    if (size == 32) {
        *insn = (uint32_t)*((uint32_t*)ptr);
    } else if (size == 16) {
        *insn = (uint32_t)*((uint16_t*)ptr);
    } else {
        assert(0);
    }

    *insn = track_iread(s, addr, paddr, *insn, size);

    return 0;
}

/* addr must be aligned */
static inline __exception int target_read_insn_u16(RISCVCPUState *s, uint16_t *pinsn,
                                                   target_ulong addr)
{
    uintptr_t mem_addend;
    uint32_t tlb_idx = (addr >> PG_SHIFT) & (TLB_SIZE - 1);

    if (likely(s->tlb_code[tlb_idx].vaddr == (addr & ~PG_MASK))) {
        mem_addend = s->tlb_code[tlb_idx].mem_addend;
        uint32_t data = *(uint16_t *)(mem_addend + (uintptr_t)addr);
#ifdef PADDR_INLINE
        *pinsn = track_iread(s, addr, s->tlb_code[tlb_idx].paddr_addend + addr, data, 16);
#else
        *pinsn = track_iread(s, addr, s->tlb_code_paddr_addend[tlb_idx] + addr, data, 16);
#endif
        return 0;
    }

    uint32_t pinsn_temp;
    if (target_read_insn_slow(s, &pinsn_temp, 16, addr))
        return -1;
    *pinsn = pinsn_temp;
    return 0;
}

static void tlb_init(RISCVCPUState *s)
{
    for (int i = 0; i < TLB_SIZE; i++) {
        s->tlb_read[i].vaddr = -1;
        s->tlb_write[i].vaddr = -1;
        s->tlb_code[i].vaddr = -1;
    }
}

static void tlb_flush_all(RISCVCPUState *s)
{
    tlb_init(s);
}

static void tlb_flush_vaddr(RISCVCPUState *s, target_ulong vaddr)
{
    tlb_flush_all(s);
}

void riscv_cpu_flush_tlb_write_range_ram(RISCVCPUState *s,
                                         uint8_t *ram_ptr,
                                         size_t ram_size)
{
    uint8_t *ram_end = ram_ptr + ram_size;
    for (int i = 0; i < TLB_SIZE; i++)
        if (s->tlb_write[i].vaddr != (target_ulong)-1) {
            uint8_t *ptr = (uint8_t *)
                (s->tlb_write[i].mem_addend + (uintptr_t)s->tlb_write[i].vaddr);
            if (ram_ptr <= ptr && ptr < ram_end)
                s->tlb_write[i].vaddr = -1;
        }
}


#define SSTATUS_MASK (  MSTATUS_SIE   \
                      | MSTATUS_SPIE  \
                      | MSTATUS_SPP   \
                      | MSTATUS_FS    \
                      | MSTATUS_SUM   \
                      | MSTATUS_MXR   \
                      | MSTATUS_UXL_MASK )

#define MSTATUS_MASK (  MSTATUS_SIE  \
                      | MSTATUS_MIE  \
                      | MSTATUS_SPIE \
                      | MSTATUS_MPIE \
                      | MSTATUS_SPP  \
                      | MSTATUS_MPP  \
                      | MSTATUS_FS   \
                      | MSTATUS_MPRV \
                      | MSTATUS_SUM  \
                      | MSTATUS_MXR  \
                      | MSTATUS_TVM  \
                      | MSTATUS_TW   \
                      | MSTATUS_TSR  \
                      | MSTATUS_UXL_MASK \
                      | MSTATUS_SXL_MASK )

/* return the complete mstatus with the SD bit */
static target_ulong get_mstatus(RISCVCPUState *s, target_ulong mask)
{
    target_ulong val;
    BOOL sd;
    val = s->mstatus | (s->fs << MSTATUS_FS_SHIFT);
    val &= mask;
    sd = ((val & MSTATUS_FS) == MSTATUS_FS) |
         ((val & MSTATUS_XS) == MSTATUS_XS);
    if (sd)
        val |= (target_ulong)1 << 63;
    return val;
}

static void set_mstatus(RISCVCPUState *s, target_ulong val)
{
    /* flush the TLBs if change of MMU config */
    target_ulong mod = s->mstatus ^ val;
    if ((mod & (MSTATUS_MPRV | MSTATUS_SUM | MSTATUS_MXR)) != 0 ||
        ((s->mstatus & MSTATUS_MPRV) && (mod & MSTATUS_MPP) != 0)) {
        tlb_flush_all(s);
    }
    s->fs = (val >> MSTATUS_FS_SHIFT) & 3;

    target_ulong mask = MSTATUS_MASK &
        ~(MSTATUS_FS | MSTATUS_UXL_MASK | MSTATUS_SXL_MASK);
    s->mstatus = s->mstatus & ~mask | val & mask;
}

static BOOL counter_access_ok(RISCVCPUState *s, uint32_t csr)
{
    uint32_t counteren = 0;

    switch (s->priv) {
    case PRV_U: counteren = s->scounteren; break;
    case PRV_S: counteren = s->mcounteren; break;
    case PRV_M: counteren = ~0; break;
    default: ;
    }

    return (counteren >> (csr & 31)) & 1;
}

/* return -1 if invalid CSR. 0 if OK. 'will_write' indicate that the
   csr will be written after (used for CSR access check) */
static int csr_read(RISCVCPUState *s, target_ulong *pval, uint32_t csr,
                     BOOL will_write)
{
    target_ulong val;

    if (((csr & 0xc00) == 0xc00) && will_write)
        return -1; /* read-only CSR */
    if (s->priv < ((csr >> 8) & 3))
        return -1; /* not enough priviledge */

    switch (csr) {
#if FLEN > 0
    case 0x001: /* fflags */
        if (s->fs == 0)
            return -1;
        val = s->fflags;
        break;
    case 0x002: /* frm */
        if (s->fs == 0)
            return -1;
        val = s->frm;
        break;
    case 0x003:
        if (s->fs == 0)
            return -1;
        val = s->fflags | (s->frm << 5);
        break;
#endif
    case 0x100:
        val = get_mstatus(s, SSTATUS_MASK);
        break;
    case 0x104: /* sie */
        val = s->mie & s->mideleg;
        break;
    case 0x105:
        val = s->stvec;
        break;
    case 0x106:
        val = s->scounteren;
        break;
    case 0x140:
        val = s->sscratch;
        break;
    case 0x141:
        val = s->sepc;
        break;
    case 0x142:
        val = s->scause;
        break;
    case 0x143:
        val = s->stval;
        break;
    case 0x144: /* sip */
        val = s->mip & s->mideleg;
        break;
    case 0x180:
        if (s->priv == PRV_S && s->mstatus & MSTATUS_TVM)
            return -1;
        val = s->satp;
        break;
    case 0x300:
        val = get_mstatus(s, (target_ulong)-1);
        break;
    case 0x301:
        val = s->misa;
        val |= (target_ulong)2 << 62;
        break;
    case 0x302:
        val = s->medeleg;
        break;
    case 0x303:
        val = s->mideleg;
        break;
    case 0x304:
        val = s->mie;
        break;
    case 0x305:
        val = s->mtvec;
        break;
    case 0x306:
        val = s->mcounteren;
        break;
    case 0x320:
        val = s->mcountinhibit;
        break;
    case 0x340:
        val = s->mscratch;
        break;
    case 0x341:
        val = s->mepc;
        break;
    case 0x342:
        val = s->mcause;
        break;
    case 0x343:
        val = s->mtval;
        break;
    case 0x344:
        val = s->mip;
        break;

    case 0x7a0: // tselect
        val = s->tselect;
        break;

    case 0x7a1: // tdata1
        val = s->tdata1[s->tselect];
        break;

    case 0x7a2: // tdata2
        val = s->tdata2[s->tselect];
        break;

    case 0x7a3: // tdata3
        val = s->tdata3[s->tselect];
        break;

    case 0x7b0:
        if (!s->debug_mode) goto invalid_csr;
        val = s->dcsr;
        break;

    case 0x7b1:
        if (!s->debug_mode) goto invalid_csr;
        val = s->dpc;
        break;

    case 0x7b2:
        if (!s->debug_mode) goto invalid_csr;
        val = s->dscratch;
        break;

    case 0xb00: /* mcycle */
    case 0xc00: /* cycle */
        if (!counter_access_ok(s, csr))
            goto invalid_csr;
        val = (int64_t)s->mcycle;
        break;

    case 0xb02: /* minstret */
    case 0xc02: /* uinstret */
        if (!counter_access_ok(s, csr))
            goto invalid_csr;
        val = (int64_t)s->minstret;
        break;
    case 0xb03:
    case 0xc03:
    case 0xb04:
    case 0xc04:
    case 0xb05:
    case 0xc05:
    case 0xb06:
    case 0xc06:
    case 0xb07:
    case 0xc07:
    case 0xb08:
    case 0xc08:
    case 0xb09:
    case 0xc09:
    case 0xb0a:
    case 0xc0a:
    case 0xb0b:
    case 0xc0b:
    case 0xb0c:
    case 0xc0c:
    case 0xb0d:
    case 0xc0d:
    case 0xb0e:
    case 0xc0e:
    case 0xb0f:
    case 0xc0f:
    case 0xb10:
    case 0xc10:
    case 0xb11:
    case 0xc11:
    case 0xb12:
    case 0xc12:
    case 0xb13:
    case 0xc13:
    case 0xb14:
    case 0xc14:
    case 0xb15:
    case 0xc15:
    case 0xb16:
    case 0xc16:
    case 0xb17:
    case 0xc17:
    case 0xb18:
    case 0xc18:
    case 0xb19:
    case 0xc19:
    case 0xb1a:
    case 0xc1a:
    case 0xb1b:
    case 0xc1b:
    case 0xb1c:
    case 0xc1c:
    case 0xb1d:
    case 0xc1d:
    case 0xb1e:
    case 0xc1e:
    case 0xb1f:
    case 0xc1f:
        if (!counter_access_ok(s, csr))
            goto invalid_csr;
        val = 0; // mhpmcounter3..31
        break;

    case 0xf14:
        val = s->mhartid;
        break;
    case 0xf13:
        val = s->mimpid;
        break;
    case 0xf12:
        val = s->marchid;
        break;
    case 0xf11:
        val = s->mvendorid;
        break;
    case 0x323:
    case 0x324:
    case 0x325:
    case 0x326:
    case 0x327:
    case 0x328:
    case 0x329:
    case 0x32a:
    case 0x32b:
    case 0x32c:
    case 0x32d:
    case 0x32e:
    case 0x32f:
    case 0x330:
    case 0x331:
    case 0x332:
    case 0x333:
    case 0x334:
    case 0x335:
    case 0x336:
    case 0x337:
    case 0x338:
    case 0x339:
    case 0x33a:
    case 0x33b:
    case 0x33c:
    case 0x33d:
    case 0x33e:
    case 0x33f:
        val = s->mhpmevent[csr & 0x1F];
        break;

    case CSR_PMPCFG(0): // NB: 1 and 3 are _illegal_ in RV64
    case CSR_PMPCFG(2):
        val = s->csr_pmpcfg[csr - CSR_PMPCFG(0)];
        break;

    case CSR_PMPADDR(0): // NB: *must* support either none or all
    case CSR_PMPADDR(1):
    case CSR_PMPADDR(2):
    case CSR_PMPADDR(3):
    case CSR_PMPADDR(4):
    case CSR_PMPADDR(5):
    case CSR_PMPADDR(6):
    case CSR_PMPADDR(7):
    case CSR_PMPADDR(8):
    case CSR_PMPADDR(9):
    case CSR_PMPADDR(10):
    case CSR_PMPADDR(11):
    case CSR_PMPADDR(12):
    case CSR_PMPADDR(13):
    case CSR_PMPADDR(14):
    case CSR_PMPADDR(15):
        val = s->csr_pmpaddr[csr - CSR_PMPADDR(0)];
        break;

    default:
    invalid_csr:
        if (s->machine->hooks.csr_read)
            return s->machine->hooks.csr_read(s, csr, pval);

#ifdef DUMP_INVALID_CSR
        /* the 'time' counter is usually emulated */
        if (csr != 0xc01 && csr != 0xc81) {
            fprintf(dromajo_stderr, "csr_read: invalid CSR=0x%x\n", csr);
        }
#endif
        *pval = 0;
        return -1;
    }
#if defined(DUMP_CSR)
    fprintf(stderr, "csr_read: hartid=%d csr=0x%03x val=0x%x\n", (int)s->mhartid, csr, (int)val);
#endif
    *pval = val;
    return 0;
}

#if FLEN > 0
static void set_frm(RISCVCPUState *s, unsigned int val)
{
    s->frm = val;
}

/* return -1 if invalid roundind mode */
static int get_insn_rm(RISCVCPUState *s, unsigned int rm)
{
    if (rm == 7)
        rm = s->frm;

    if (rm >= 5)
        return -1;
    else
        return rm;
}
#endif

static void unpack_pmpaddrs(RISCVCPUState *s)
{
    uint8_t cfg;
    s->pmp_n = 0;

    for (int i = 0; i < 16; ++i) {
        if (i < 8)
            cfg = s->csr_pmpcfg[0] >> (i * 8);
        else
            cfg = s->csr_pmpcfg[2] >> ((i - 8) * 8);

        switch (cfg & PMPCFG_A_MASK) {
        case PMPCFG_A_OFF:
            break;

        case PMPCFG_A_TOR:
            s->pmpcfg[s->pmp_n] = cfg;
            s->pmp[s->pmp_n].lo = i == 0 ? 0 : s->csr_pmpaddr[i-1] << 2;
            s->pmp[s->pmp_n].hi = s->csr_pmpaddr[i] << 2;
            s->pmp_n++;
            break;

        case PMPCFG_A_NA4:
            s->pmpcfg[s->pmp_n] = cfg;
            s->pmp[s->pmp_n].lo = s->csr_pmpaddr[i] << 2;
            s->pmp[s->pmp_n].hi = (s->csr_pmpaddr[i] << 2) + 4;
            s->pmp_n++;
            break;

        case PMPCFG_A_NAPOT: {
            s->pmpcfg[s->pmp_n] = cfg;
            int j;
            // Count trailing ones
            for (j = 0; j < 64; ++j)
                if ((s->csr_pmpaddr[i] & (1 << j)) == 0)
                    break;
            j += 3; // 8-byte is the lowest option
            // NB, meaningless when i >= 56!
            if (j >= 64) {
                s->pmp[s->pmp_n].lo = 0;
                s->pmp[s->pmp_n].hi = ~0ll;
            } else {
                s->pmp[s->pmp_n].lo = (s->csr_pmpaddr[i] << 2) & ~((1llu << j) - 1);
                s->pmp[s->pmp_n].hi = s->pmp[s->pmp_n].lo + (1llu << j);
                if (s->pmp[s->pmp_n].hi <= s->pmp[s->pmp_n].lo)
                    // Overflowed
                    s->pmp[s->pmp_n].hi = ~0ll;
            }
            s->pmp_n++;
            break;
        }
        }
    }

    tlb_flush_all(s); // The TLB partically caches PMP decisions
}

/* return -1 if invalid CSR, 0 if OK, -2 if CSR raised an exception,
 * 2 if TLBs have been flushed. */
static int csr_write(RISCVCPUState *s, uint32_t csr, target_ulong val)
{
    target_ulong mask;

#if defined(DUMP_CSR)
    fprintf(dromajo_stderr, "csr_write: hardid=%d csr=0x%03x val=0x", (int)s->mhartid, csr);
    print_target_ulong(val);
    fprintf(dromajo_stderr, "\n");
#endif
    switch (csr) {
#if FLEN > 0
    case 0x001: /* fflags */
        s->fflags = val & 0x1f;
        s->fs = 3;
        break;
    case 0x002: /* frm */
        set_frm(s, val & 7);
        s->fs = 3;
        break;
    case 0x003: /* fcsr */
        set_frm(s, (val >> 5) & 7);
        s->fflags = val & 0x1f;
        s->fs = 3;
        break;
#endif
    case 0x100: /* sstatus */
        set_mstatus(s, s->mstatus & ~SSTATUS_MASK | val & SSTATUS_MASK);
        break;
    case 0x104: /* sie */
        mask = s->mideleg;
        s->mie = s->mie & ~mask | val & mask;
        break;
    case 0x105:
        // enforce 256-byte alignment for vectored interrupts
        if (val & 1) val &= ~255 + 1;
        s->stvec = val & ~2;
        break;
    case 0x106:
        s->scounteren = val;
        break;
    case 0x140:
        s->sscratch = val;
        break;
    case 0x141:
        s->sepc = val & (s->misa & MCPUID_C ? ~1 : ~3);
        s->sepc = SEPC_TRUNCATE(s->sepc);
        break;
    case 0x142:
        s->scause = val & SCAUSE_MASK;
        break;
    case 0x143:
        s->stval = STVAL_TRUNCATE(val);
        break;
    case 0x144: /* sip */
        mask = s->mideleg;
        s->mip = s->mip & ~mask | val & mask;
        break;
    case 0x180:
        if (s->priv == PRV_S && s->mstatus & MSTATUS_TVM)
            return -1;
        {
            uint64_t mode = (val >> 60) & 15;
            if (mode == 0 || mode == 8 || mode == 9)
                s->satp = val & SATP_MASK;
        }
        /* no ASID implemented [yet] */
        tlb_flush_all(s);
        return 2;

    case 0x300:
        set_mstatus(s, val);
        break;
    case 0x301: /* misa */
        /* We don't support changing misa */
        break;
    case 0x302: {
        target_ulong mask = 0xB109; // matching Spike
        s->medeleg = s->medeleg & ~mask | val & mask;
        break;
    }
    case 0x303:
        mask = MIP_SSIP | MIP_STIP | MIP_SEIP;
        s->mideleg = s->mideleg & ~mask | val & mask;
        break;
    case 0x304:
        mask = MIE_MCIP /*| MIE_SCIP | MIE_UCIP*/ | MIE_MEIE | MIE_SEIE /*| MIE_UEIE*/ | MIE_MTIE | MIE_STIE | /*MIE_UTIE | */ MIE_MSIE | MIE_SSIE /*| MIE_USIE */;
        s->mie = s->mie & ~mask | val & mask;
        break;
    case 0x305:
        // enforce 256-byte alignment for vectored interrupts
        if (val & 1) val &= ~255 + 1;
        s->mtvec = val & ((1ull << s->physical_addr_len) - 3); // mtvec[1] === 0
        break;
    case 0x306:
        s->mcounteren = val;
        break;
    case 0x320:
        s->mcountinhibit = val & ~2;
        break;
    case 0x340:
        s->mscratch = val;
        break;
    case 0x341:
        s->mepc = val & (s->misa & MCPUID_C ? ~1 : ~3);
        s->mepc = MEPC_TRUNCATE(s->mepc);
        break;
    case 0x342:
        s->mcause = val & MCAUSE_MASK;
        break;
    case 0x343:
        s->mtval = MTVAL_TRUNCATE(val);
        break;
    case 0x344:
        mask = /* MEIP | */ MIP_SEIP | /*MIP_UEIP | MTIP | */ MIP_STIP | /*MIP_UTIP | MSIP | */ MIP_SSIP /*| MIP_USIP*/;
        s->mip = s->mip & ~mask | val & mask;
        break;

    case 0x7a0: // tselect
        s->tselect = val % MAX_TRIGGERS;
        break;

    case 0x7a1: // tdata1
        // Only support No Trigger and MControl
        {
            int type = val >> 60;
            if (type != 0 && type != 2)
                break;
            // SW can write type and mcontrol bits M and EXECUTE
            mask = ((target_ulong)15 << 60) | MCONTROL_M | MCONTROL_EXECUTE;
            s->tdata1[s->tselect] = s->tdata1[s->tselect] & ~mask | val & mask;
        }
        break;

    case 0x7a2: // tdata2
        s->tdata2[s->tselect] = val;
        break;

    case 0x7a3: // tdata3
        s->tdata3[s->tselect] = val;
        break;

    case 0x7b0:
        if (!s->debug_mode) goto invalid_csr;
        /* XXX We have a very incomplete implementation of debug mode, only just enough
           to restore a snapshot and stop counters */
        mask = 0x603; // stopcount and stoptime && also the priv level to return
        s->dcsr = s->dcsr & ~mask | val & mask;
        s->stop_the_counter = s->dcsr & 0x600 != 0;
        break;

    case 0x7b1:
        if (!s->debug_mode) goto invalid_csr;
        s->dpc = val & (s->misa & MCPUID_C ? ~1 : ~3);
        break;

    case 0x7b2:
        if (!s->debug_mode) goto invalid_csr;
        s->dscratch = val;
        break;

    case 0x323:
    case 0x324:
    case 0x325:
    case 0x326:
    case 0x327:
    case 0x328:
    case 0x329:
    case 0x32a:
    case 0x32b:
    case 0x32c:
    case 0x32d:
    case 0x32e:
    case 0x32f:
    case 0x330:
    case 0x331:
    case 0x332:
    case 0x333:
    case 0x334:
    case 0x335:
    case 0x336:
    case 0x337:
    case 0x338:
    case 0x339:
    case 0x33a:
    case 0x33b:
    case 0x33c:
    case 0x33d:
    case 0x33e:
    case 0x33f:
        s->mhpmevent[csr & 0x1F] = val & (HPM_EVENT_SETMASK | HPM_EVENT_EVENTMASK);
        break;

    case CSR_PMPCFG(0): // NB: 1 and 3 are _illegal_ in RV64
    case CSR_PMPCFG(2): {
        assert(PMP_N % 8 == 0);
        int      c    = csr - CSR_PMPCFG(0);

        if (PMP_N <= c/2 * 8)
            break;

        uint64_t orig = s->csr_pmpcfg[c];
        uint64_t new_val  = 0;

        for (int i = 0; i < 8; ++i) {
            uint64_t cfg = (orig >> (i * 8)) & 255;
            if ((cfg & PMPCFG_L) == 0)
                cfg = (val >> (i * 8)) & 255;
            cfg &= ~PMPCFG_RES;
            new_val |= cfg << (i * 8);
        }

        s->csr_pmpcfg[c] = new_val;

        unpack_pmpaddrs(s);
        break;
    }

    case CSR_PMPADDR(0): // NB: *must* support either none or all
    case CSR_PMPADDR(1):
    case CSR_PMPADDR(2):
    case CSR_PMPADDR(3):
    case CSR_PMPADDR(4):
    case CSR_PMPADDR(5):
    case CSR_PMPADDR(6):
    case CSR_PMPADDR(7):
    case CSR_PMPADDR(8):
    case CSR_PMPADDR(9):
    case CSR_PMPADDR(10):
    case CSR_PMPADDR(11):
    case CSR_PMPADDR(12):
    case CSR_PMPADDR(13):
    case CSR_PMPADDR(14):
    case CSR_PMPADDR(15):
        if (PMP_N <= csr - CSR_PMPADDR(0))
            break;

        // Note, due to TOR ranges, one PMPADDR can affect two entries
        // but we just recalculate all of them
        s->csr_pmpaddr[csr - CSR_PMPADDR(0)] = val & PMPADDR_MASK;
        unpack_pmpaddrs(s);
        break;

    case 0xb00: /* mcycle */
        s->mcycle = val;
        break;
    case 0xb02: /* minstret */
        s->minstret = val;
        break;
    case 0xb03:
    case 0xb04:
    case 0xb05:
    case 0xb06:
    case 0xb07:
    case 0xb08:
    case 0xb09:
    case 0xb0a:
    case 0xb0b:
    case 0xb0c:
    case 0xb0d:
    case 0xb0e:
    case 0xb0f:
    case 0xb10:
    case 0xb11:
    case 0xb12:
    case 0xb13:
    case 0xb14:
    case 0xb15:
    case 0xb16:
    case 0xb17:
    case 0xb18:
    case 0xb19:
    case 0xb1a:
    case 0xb1b:
    case 0xb1c:
    case 0xb1d:
    case 0xb1e:
    case 0xb1f:
        // Allow, but ignore to write to performance counters mhpmcounter
        break;

    default:
        if (s->machine->hooks.csr_write)
            return s->machine->hooks.csr_write(s, csr, val);

    invalid_csr:
#ifdef DUMP_INVALID_CSR
        fprintf(dromajo_stderr, "csr_write: invalid CSR=0x%x\n", csr);
#endif
        return -1;
    }
    return 0;
}

static void set_priv(RISCVCPUState *s, int priv)
{
    if (s->priv != priv) {
        tlb_flush_all(s);
        s->priv = priv;
    }
}

static void raise_exception2(RISCVCPUState *s, uint64_t cause,
                             target_ulong tval)
{
    BOOL deleg;

#if defined(DUMP_EXCEPTIONS)
    const static char *cause_s[] = {
        "misaligned_fetch",
        "fault_fetch",
        "illegal_instruction",
        "breakpoint",
        "misaligned_load",
        "fault_load",
        "misaligned_store",
        "fault_store",
        "user_ecall",
        "<reserved (supervisor_ecall?)>",
        "<reserved (hypervisor_ecall?)>",
        "<reserved (machine_ecall?)>",
        "fetch_page_fault",
        "load_page_fault",
        "<reserved_14>",
        "store_page_fault",
    };

    if (cause & CAUSE_INTERRUPT)
        fprintf(dromajo_stderr, "hartid=%d: exception interrupt #%d, epc 0x%016jx\n",
                (int)s->mhartid, cause & 63, (uintmax_t)s->pc);
    else if (cause <= CAUSE_STORE_PAGE_FAULT) {
        fprintf(dromajo_stderr, "hartid=%d priv: %d exception %s, epc 0x%016jx\n",
               (int)s->mhartid, s->priv, cause_s[cause], (uintmax_t)s->pc);
        fprintf(dromajo_stderr, "hartid=%d0           tval 0x%016jx\n", (int)s->mhartid, (uintmax_t)tval);
    } else {
        fprintf(dromajo_stderr, "hartid=%d: exception %d, epc 0x%016jx\n",
               (int)s->mhartid, cause, (uintmax_t)s->pc);
        fprintf(dromajo_stderr, "hartid=%d:           tval 0x%016jx\n", (int)s->mhartid, (uintmax_t)tval);
    }
#endif

    if (s->priv <= PRV_S) {
        /* delegate the exception to the supervisor priviledge */
        if (cause & CAUSE_INTERRUPT)
            deleg = (s->mideleg >> (cause & 63)) & 1;
        else
            deleg = (s->medeleg >> cause) & 1;
    } else {
        deleg = 0;
    }

    target_ulong effective_tvec;

    if (deleg) {
        s->scause = cause;
        s->sepc = SEPC_TRUNCATE(s->pc);
        s->stval = STVAL_TRUNCATE(tval);
        s->mstatus = (s->mstatus & ~MSTATUS_SPIE) |
            (!!(s->mstatus & MSTATUS_SIE) << MSTATUS_SPIE_SHIFT);
        s->mstatus = (s->mstatus & ~MSTATUS_SPP) |
            (s->priv << MSTATUS_SPP_SHIFT);
        s->mstatus &= ~MSTATUS_SIE;
        set_priv(s, PRV_S);
        effective_tvec = s->stvec;
    } else {
        s->mcause = cause;
        s->mepc = MEPC_TRUNCATE(s->pc);
        s->mtval = MTVAL_TRUNCATE(tval);

        /* When a trap is taken from privilege mode y into privilege
           mode x, xPIE is set to the value of xIE; xIE is set to 0;
           and xPP is set to y.

           Here x = M, thus MPIE = MIE; MIE = 0; MPP = s->priv
        */

        s->mstatus = (s->mstatus & ~MSTATUS_MPIE) |
            (!!(s->mstatus & MSTATUS_MIE) << MSTATUS_MPIE_SHIFT);

        s->mstatus = (s->mstatus & ~MSTATUS_MPP) |
            (s->priv << MSTATUS_MPP_SHIFT);
        s->mstatus &= ~MSTATUS_MIE;
        set_priv(s, PRV_M);
        effective_tvec = s->mtvec;
    }

    int mode = effective_tvec & 3;
    target_ulong base = effective_tvec & ~3;
    s->pc = base;
    if (mode == 1 && cause & CAUSE_INTERRUPT)
        s->pc += 4 * (cause & ~CAUSE_INTERRUPT);
}

static void raise_exception(RISCVCPUState *s, uint64_t cause)
{
    raise_exception2(s, cause, 0);
}

static void handle_sret(RISCVCPUState *s)
{

    /* Copy down SPIE to SIE and set SPIE */
    s->mstatus &= ~MSTATUS_SIE;
    s->mstatus |= (s->mstatus >> 4) & MSTATUS_SIE;
    s->mstatus |= MSTATUS_SPIE;

    int spp = (s->mstatus & MSTATUS_SPP) >> MSTATUS_SPP_SHIFT;
    s->mstatus &= ~MSTATUS_SPP;

    set_priv(s, spp);
    s->pc = s->sepc;
}

static void handle_mret(RISCVCPUState *s)
{
    /* Copy down MPIE to MIE and set MPIE */
    s->mstatus &= ~MSTATUS_MIE;
    s->mstatus |= (s->mstatus >> 4) & MSTATUS_MIE;
    s->mstatus |= MSTATUS_MPIE;

    int mpp = (s->mstatus & MSTATUS_MPP) >> MSTATUS_MPP_SHIFT;
    s->mstatus &= ~MSTATUS_MPP;

    set_priv(s, mpp);
    s->pc = s->mepc;
}

static void handle_dret(RISCVCPUState *s)
{
    s->stop_the_counter = FALSE; // Enable counters again
    s->debug_mode = FALSE;
    set_priv(s, s->dcsr & 3);
    s->pc = s->dpc;
}

static inline uint32_t get_pending_irq_mask(RISCVCPUState *s)
{
    uint32_t pending_ints, enabled_ints;

    pending_ints = s->mip & s->mie;
    if (pending_ints == 0)
        return 0;

    enabled_ints = 0;
    switch (s->priv) {
    case PRV_M:
        if (s->mstatus & MSTATUS_MIE)
            enabled_ints = ~s->mideleg;
        break;
    case PRV_S:
        enabled_ints = ~s->mideleg;
        if (s->mstatus & MSTATUS_SIE)
            enabled_ints |= s->mideleg;
        break;
    default:
    case PRV_U:
        enabled_ints = -1;
        break;
    }
    return pending_ints & enabled_ints;
}

static __exception int raise_interrupt(RISCVCPUState *s)
{
    uint32_t mask;
    int irq_num;

    mask = get_pending_irq_mask(s);
    if (mask == 0)
        return 0;
    irq_num = ctz32(mask);
#ifdef DUMP_INTERRUPTS
    fprintf(dromajo_stderr,
            "raise_interrupt: irq=%d priv=%d pc=%llx hartid=%d\n",
            irq_num, s->priv, (unsigned long long)s->pc, (int)s->mhartid);
#endif

    raise_exception(s, irq_num | CAUSE_INTERRUPT);
    return -1;
}

static inline int32_t sext(int32_t val, int n)
{
    return (val << (32 - n)) >> (32 - n);
}

static inline uint32_t get_field1(uint32_t val, int src_pos,
                                  int dst_pos, int dst_pos_max)
{
    int mask;
    assert(dst_pos_max >= dst_pos);
    mask = ((1 << (dst_pos_max - dst_pos + 1)) - 1) << dst_pos;
    if (dst_pos >= src_pos)
        return (val << (dst_pos - src_pos)) & mask;
    else
        return (val >> (src_pos - dst_pos)) & mask;
}

static inline RISCVCTFInfo ctf_compute_hint(int rd, int rs1)
{
    int rd_link  = rd  == 1 || rd  == 5;
    int rs1_link = rs1 == 1 || rs1 == 5;
    RISCVCTFInfo k = (RISCVCTFInfo)(rd_link * 2 + rs1_link + (int)ctf_taken_jalr);

    if (k == ctf_taken_jalr_pop_push && rs1 == rd)
        return ctf_taken_jalr_push;

    return k;
}


/*
 * While the 32-bit QNAN is defined in softfp.h, we need it here to
 * pull f_unbox{32,64} out of the fragile macro magic.
 */
static const sfloat64 f_qnan32 = 0x7fc00000;

static sfloat64 f_unbox32(sfloat64 r)
{
    if ((r & F32_HIGH) != F32_HIGH)
        return f_qnan32;

    return r;
}

static sfloat64 f_unbox64(sfloat64 r)
{
    return r;
}

#define XLEN 32
#include "dromajo_template.h"

#define XLEN 64
#include "dromajo_template.h"

int riscv_cpu_interp(RISCVCPUState *s, int n_cycles)
{
    return riscv_cpu_interp64(s, n_cycles);
}

/* Note: the value is not accurate when called in riscv_cpu_interp() */
uint64_t riscv_cpu_get_cycles(RISCVCPUState *s)
{
    return s->mcycle;
}

void riscv_cpu_set_mip(RISCVCPUState *s, uint32_t mask)
{
    s->mip |= mask;
    /* exit from power down if an interrupt is pending */
    if (s->power_down_flag && (s->mip & s->mie) != 0 && (s->machine->common.pending_interrupt != -1 || !s->machine->common.cosim))
        s->power_down_flag = FALSE;
}

void riscv_cpu_reset_mip(RISCVCPUState *s, uint32_t mask)
{
    s->mip &= ~mask;
}

uint32_t riscv_cpu_get_mip(RISCVCPUState *s)
{
    return s->mip;
}

BOOL riscv_cpu_get_power_down(RISCVCPUState *s)
{
    return s->power_down_flag;
}

RISCVCPUState *riscv_cpu_init(RISCVMachine *machine, int hartid)
{
    RISCVCPUState *s = (RISCVCPUState *)mallocz(sizeof *s);
    s->machine = machine;
    s->mem_map = machine->mem_map;
    s->pc = machine->reset_vector;
    s->priv = PRV_M;
    s->mstatus = ((uint64_t)2 << MSTATUS_UXL_SHIFT) |
                 ((uint64_t)2 << MSTATUS_SXL_SHIFT) |
                 (3 << MSTATUS_MPP_SHIFT);
    s->plic_enable_irq = 0;
    s->misa |= MCPUID_SUPER | MCPUID_USER | MCPUID_I | MCPUID_M | MCPUID_A;
    s->most_recently_written_reg = -1;
#if FLEN >= 32
    s->most_recently_written_fp_reg = -1;
    s->misa |= MCPUID_F;
#endif
#if FLEN >= 64
    s->misa |= MCPUID_D;
#endif
#if FLEN >= 128
    s->misa |= MCPUID_Q;
#endif
    s->misa |= MCPUID_C;

    if (machine->custom_extension)
        s->misa |= MCPUID_X;

    s->mvendorid = 11 * 128 + 101; // Esperanto JEDEC number 101 in bank 11 (Change for your own)
    s->marchid   = (1ULL << 63) | 2;
    s->mimpid    = 1;
    s->mhartid   = hartid;

    s->tselect = 0;
    for (int i = 0; i < MAX_TRIGGERS; ++i) {
        s->tdata1[i] = 2l << 60;
        s->tdata2[i] = ~(target_ulong)0;
    }

    tlb_init(s);

    // Exit code of the user-space benchmark app
    s->benchmark_exit_code = 0;

    return s;
}

void riscv_cpu_end(RISCVCPUState *s)
{
    free(s);
}

void riscv_set_pc(RISCVCPUState *s, uint64_t val)
{
    s->pc = val & (s->misa & MCPUID_C ? ~1 : ~3);
}

uint64_t riscv_get_pc(RISCVCPUState *s)
{
    return s->pc;
}

uint64_t riscv_get_reg(RISCVCPUState *s, int rn)
{
    assert(0 <= rn && rn < 32);
    return s->reg[rn];
}

uint64_t riscv_get_reg_previous(RISCVCPUState *s, int rn)
{
    assert(0 <= rn && rn < 32);
    return s->reg_prior[rn];
}


void riscv_repair_csr(RISCVCPUState *s, uint32_t reg_num, uint64_t csr_num, uint64_t csr_val)
{
    switch (csr_num & 0xFFF) {
    case 0xb00:
    case 0xc00: // mcycle
        s->mcycle       = csr_val;
        s->reg[reg_num] = csr_val;
        break;
    case 0xb02:
    case 0xc02: // minstret
        s->minstret     = csr_val;
        s->reg[reg_num] = csr_val;
        break;

    default:
        fprintf(dromajo_stderr, "riscv_repair_csr: This CSR is unsupported for repairing: %lx\n",
                (unsigned long)csr_num);
        break;
    }
}

/* Sync up the shadow register state if there are no errors */
void riscv_cpu_sync_regs(RISCVCPUState *s)
{
    for (int i = 1; i < 32; ++i) {
        s->reg_prior[i] = s->reg[i];
    }
}

uint64_t riscv_cpu_get_mstatus(RISCVCPUState* s)
{
    return get_mstatus(s, MSTATUS_MASK);
}

uint64_t riscv_cpu_get_medeleg(RISCVCPUState* s)
{
    return s->medeleg;
}

uint64_t riscv_get_fpreg(RISCVCPUState *s, int rn)
{
    assert(0 <= rn && rn < 32);
    return s->fp_reg[rn];
}

void riscv_set_reg(RISCVCPUState *s, int rn, uint64_t val)
{
    assert(0 < rn && rn < 32);
    s->reg[rn] = val;
}

void riscv_dump_regs(RISCVCPUState *s)
{
    dump_regs(s);
}

int riscv_read_insn(RISCVCPUState *s, uint32_t *insn, uint64_t addr)
{
    /* target_read_insn_slow() wasn't designed for being used outside
       execution and will potentially raise exceptions.  Unfortunately
       fixing this correctly is invasive so we just protect the
       affected state. */

    int          saved_pending_exception = s->pending_exception;
    target_ulong saved_pending_tval      = s->pending_tval;
    int          res                     = target_read_insn_slow(s, insn, 32, addr);
    s->pending_exception                 = saved_pending_exception;
    s->pending_tval                      = saved_pending_tval;

    return res;
}

uint32_t riscv_cpu_get_misa(RISCVCPUState *s)
{
    return s->misa;
}

int riscv_get_priv_level(RISCVCPUState *s)
{
    return s->priv;
}

int riscv_get_most_recently_written_reg(RISCVCPUState *s)
{
    return s->most_recently_written_reg;
}

int riscv_get_most_recently_written_fp_reg(RISCVCPUState *s)
{
    return s->most_recently_written_fp_reg;
}

int riscv_benchmark_exit_code(RISCVCPUState *s)
{
    return s->benchmark_exit_code;
}

void riscv_get_ctf_info(RISCVCPUState *s, RISCVCTFInfo *info)
{
    *info = s->info;
}

void riscv_get_ctf_target(RISCVCPUState *s, uint64_t *target)
{
    *target = s->next_addr;
}

BOOL riscv_terminated(RISCVCPUState *s)
{
    return s->terminate_simulation;
}

void riscv_set_debug_mode(RISCVCPUState *s, bool on)
{
    s->debug_mode = on;
}

static void serialize_memory(const void *base, size_t size, const char *file)
{
    int f_fd = open(file, O_CREAT | O_WRONLY | O_TRUNC, 0777);

    if (f_fd < 0)
        err(-3, "trying to write %s", file);

    while (size) {
        ssize_t written = write(f_fd, base, size);
        if (written <= 0)
            err(-3, "while writing %s", file);
        size -= written;
    }

    close(f_fd);
}

static void deserialize_memory(void *base, size_t size, const char *file)
{
    int f_fd = open(file, O_RDONLY);

    if (f_fd < 0)
        err(-3, "trying to read %s", file);

    size_t sz = read(f_fd, base, size);

    if (sz != size)
        err(-3, "%s %zd size does not match memory size %zd", file, sz, size);

    close(f_fd);
}

static void dump_hex_memory(const void *base, size_t size, const char *file)
{
    uint8_t* mem_pointer = (uint8_t*)base;

    std::ofstream hex_file;
    hex_file.open(file);

    int num_bytes = 8;
    uint32_t iter = 0;
    while (size) {
        // format
        uint32_t buffer1=0;
        uint32_t buffer2=0;
        for (int i=0; i<num_bytes; i++) {
          uint8_t b = *(mem_pointer);
          mem_pointer++;
          if (i < num_bytes/2) {
            buffer1 = buffer1 | (b << 8*i);
          } else {
            buffer2 = buffer2 | (b << 8*(i-num_bytes/2));
          }
        }
        // dump if non-zero
        if (buffer1 > 0 || buffer2 > 0) {
          hex_file << std::dec << iter << " ";
          hex_file << std::hex << std::setfill('0') << std::setw(8) << buffer2;
          hex_file << std::hex << std::setfill('0') << std::setw(8) << buffer1;
          hex_file << std::endl;
        }

        size-=num_bytes;
        iter++;
    }

    hex_file.close();
}

static uint32_t create_csrrw(int rs, uint32_t csrn)
{
    return 0x1073 | ((csrn & 0xFFF) << 20) | ((rs & 0x1F) << 15);
}

static uint32_t create_csrrs(int rd, uint32_t csrn)
{
    return 0x2073 | ((csrn & 0xFFF) << 20) | ((rd & 0x1F) << 7);
}

static uint32_t create_auipc(int rd, uint32_t addr)
{
    if (addr & 0x800)
        addr += 0x800;

    return 0x17 | ((rd & 0x1F) << 7) | ((addr >> 12) << 12);
}

static uint32_t create_addi(int rd, uint32_t addr)
{
    uint32_t pos = addr & 0xFFF;

    return 0x13 | ((rd & 0x1F) << 7) | ((rd & 0x1F) << 15) | ((pos & 0xFFF) << 20);
}

static uint32_t create_seti(int rd, uint32_t data)
{
    return 0x13 | ((rd & 0x1F) << 7) | ((data & 0xFFF) << 20);
}

static uint32_t create_ld(int rd, int rs1)
{
    return 3 | ((rd & 0x1F) << 7) | (3 << 12) | ((rs1 & 0x1F) << 15);
}

static uint32_t create_sd(int rs1, int rs2)
{
    return 0x23 | ((rs2 & 0x1F) << 20) | (3 << 12) | ((rs1 & 0x1F) << 15);
}

static uint32_t create_fld(int rd, int rs1)
{
    return 7 | ((rd & 0x1F) << 7) | (0x3<<12) | ((rs1 & 0x1F) << 15);
}

static bool skip_csr_recovery(RISCVCPUState *s, uint32_t csrn)
{
    for (uint64_t i = 0; i < s->machine->missing_csrs_size; i++) {
        if (s->machine->missing_csrs[i] == csrn) {
            return true;
        }
    }

    return false;
}

static void create_csr12_recovery(uint32_t *rom, uint32_t *code_pos, uint32_t csrn, uint16_t val, RISCVCPUState *s)
{
    if (skip_csr_recovery(s, csrn))
        return;

    rom[(*code_pos)++] = create_seti(1, val & 0xFFF);
    rom[(*code_pos)++] = create_csrrw(1, csrn);
}

#ifdef LIVECACHE
static void create_read_warmup(uint32_t *rom, uint32_t *code_pos, uint32_t *data_pos, uint64_t val)
{
    uint32_t data_off = sizeof(uint32_t) * (*data_pos - *code_pos);

    rom[(*code_pos)++] = create_auipc(1, data_off);
    rom[(*code_pos)++] = create_addi(1, data_off);
    rom[(*code_pos)++] = create_ld(1, 1);
    rom[(*code_pos)++] = create_ld(1, 1);

    rom[(*data_pos)++] = val & 0xFFFFFFFF;
    rom[(*data_pos)++] = val >> 32;
}
#endif

static void create_csr64_recovery(uint32_t *rom, uint32_t *code_pos, uint32_t *data_pos, uint32_t csrn, uint64_t val, RISCVCPUState *s)
{
    if (skip_csr_recovery(s, csrn))
        return;

    uint32_t data_off = sizeof(uint32_t) * (*data_pos - *code_pos);

    rom[(*code_pos)++] = create_auipc(1, data_off);
    rom[(*code_pos)++] = create_addi(1, data_off);
    rom[(*code_pos)++] = create_ld(1, 1);
    rom[(*code_pos)++] = create_csrrw(1, csrn);

    rom[(*data_pos)++] = val & 0xFFFFFFFF;
    rom[(*data_pos)++] = val >> 32;
}

static void create_reg_recovery(uint32_t *rom, uint32_t *code_pos, uint32_t *data_pos, int rn, uint64_t val)
{
    uint32_t data_off = sizeof(uint32_t) * (*data_pos - *code_pos);

    rom[(*code_pos)++] = create_auipc(rn, data_off);
    rom[(*code_pos)++] = create_addi(rn, data_off);
    rom[(*code_pos)++] = create_ld(rn, rn);

    rom[(*data_pos)++] = val & 0xFFFFFFFF;
    rom[(*data_pos)++] = val >> 32;
}

static void create_io64_recovery(uint32_t *rom, uint32_t *code_pos, uint32_t *data_pos, uint64_t addr, uint64_t val)
{
    uint32_t data_off = sizeof(uint32_t) * (*data_pos - *code_pos);

    rom[(*code_pos)++] = create_auipc(1, data_off);
    rom[(*code_pos)++] = create_addi(1, data_off);
    rom[(*code_pos)++] = create_ld(1, 1);

    rom[(*data_pos)++] = addr & 0xFFFFFFFF;
    rom[(*data_pos)++] = addr >> 32;

    uint32_t data_off2 = sizeof(uint32_t) * (*data_pos - *code_pos);
    rom[(*code_pos)++] = create_auipc(2, data_off2);
    rom[(*code_pos)++] = create_addi(2, data_off2);
    rom[(*code_pos)++] = create_ld(2, 2);

    rom[(*code_pos)++] = create_sd(1, 2);

    rom[(*data_pos)++] = val & 0xFFFFFFFF;
    rom[(*data_pos)++] = val >> 32;
}

static void create_hang_nonzero_hart(uint32_t *rom, uint32_t *code_pos, uint32_t *data_pos)
{
    /* Note, this matches the boot loader prologue from copy_kernel() */

    rom[(*code_pos)++] = 0xf1402573;  // start:  csrr   a0, mhartid
    rom[(*code_pos)++] = 0x00050663;  //         beqz   a0, 1f
    rom[(*code_pos)++] = 0x10500073;  // 0:      wfi
    rom[(*code_pos)++] = 0xffdff06f;  //         j      0b
                                      // 1:
}

static void create_boot_rom(RISCVCPUState *s, const char *file, const uint64_t clint_base_addr)
{
    uint32_t rom[ROM_SIZE / 4];
    memset(rom, 0, sizeof rom);

    // ROM organization
    // 0000..003F wasted
    // 0040..0AFF boot code (2,752 B)
    // 0B00..0FFF boot data (  512 B)

    uint32_t code_pos = (BOOT_BASE_ADDR - ROM_BASE_ADDR) / sizeof *rom;
    uint32_t data_pos = 0xB00 / sizeof *rom;
    uint32_t data_pos_start = data_pos;

    if (s->machine->ncpus == 1) // FIXME: May be interesting to freeze hartid >= ncpus
        create_hang_nonzero_hart(rom, &code_pos, &data_pos);

    create_csr64_recovery(rom, &code_pos, &data_pos, 0x7b1, s->pc, s); // Write to DPC (CSR, 0x7b1)

    // Write current priviliege level to prv in dcsr (0 user, 1 supervisor, 2 user)
    // dcsr is at 0x7b0 prv is bits 0 & 1
    // dcsr.stopcount = 1
    // dcsr.stoptime  = 1
    // dcsr = 0x600 | (PrivLevel & 0x3)
    if (s->priv == 2) {
        fprintf(dromajo_stderr, "UNSUPORTED Priv mode (no hyper)\n");
        exit(-4);
    }

    create_csr12_recovery(rom, &code_pos, 0x7b0, 0x600 | s->priv, s);

#ifdef LIVECACHE
    int addr_size;
    uint64_t *addr = s->machine->llc->traverse(addr_size);

    if (addr_size > ROM_SIZE / 4) {
        fprintf(stderr, "LiveCache: truncating boot rom from %d to %d\n", addr_size, ROM_SIZE / 4);
        addr_size = ROM_SIZE/4;
    }

    for (int i = 0; i < addr_size; ++i) {
        uint64_t a = addr[i] & ~0x1ULL;
        printf("addr:%llx %s\n", (unsigned long long)a, (addr[i] & 1) ? "ST" : "LD");
        create_read_warmup(rom, &code_pos, &data_pos, a); // treat write like reads for the moment
    }
#endif

    // NOTE: mstatus & misa should be one of the first because risvemu breaks down this
    // register for performance reasons. E.g: restoring the fflags also changes
    // parts of the mstats
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x300, get_mstatus(s, (target_ulong)-1), s); // mstatus
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x301, s->misa | ((target_ulong)2 << 62), s); // misa

    // All the remaining CSRs
    if (s->fs) { // If the FPU is down, you can not recover flags
        create_csr12_recovery(rom, &code_pos, 0x001, s->fflags, s);
        // Only if fflags, otherwise it would raise an illegal instruction
        create_csr12_recovery(rom, &code_pos, 0x002, s->frm, s);
        create_csr12_recovery(rom, &code_pos, 0x003, s->fflags | (s->frm << 5), s);

        // do the FP registers, iff fs is set
        for (int i = 0; i < 32; i++) {
            uint32_t data_off = sizeof(uint32_t) * (data_pos - code_pos);
            rom[code_pos++] = create_auipc(1, data_off);
            rom[code_pos++] = create_addi(1, data_off);
            rom[code_pos++] = create_fld(i, 1);

            rom[data_pos++] = (uint32_t)s->fp_reg[i];
            rom[data_pos++] = (uint64_t)s->reg[i] >> 32;
        }
    }

    // Recover CPU CSRs

    // Cycle and instruction are alias across modes. Just write to m-mode counter
    // Already done before CLINT. create_csr64_recovery(rom, &code_pos, &data_pos, 0xb00, s->insn_counter); // mcycle
    //create_csr64_recovery(rom, &code_pos, &data_pos, 0xb02, s->insn_counter); // instret

    for (int i = 3; i < 32 ; ++i) {
      create_csr12_recovery(rom, &code_pos, 0xb00 + i, 0, s); // reset mhpmcounter3..31
      create_csr64_recovery(rom, &code_pos, &data_pos, 0x320 + i, s->mhpmevent[i], s); // mhpmevent3..31
    }
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x7a0, s->tselect, s); // tselect
    //FIXME: create_csr64_recovery(rom, &code_pos, &data_pos, 0x7a1, s->tdata1); // tdata1
    //FIXME: create_csr64_recovery(rom, &code_pos, &data_pos, 0x7a2, s->tdata2); // tdata2
    //FIXME: create_csr64_recovery(rom, &code_pos, &data_pos, 0x7a3, s->tdata3); // tdata3

    create_csr64_recovery(rom, &code_pos, &data_pos, 0x302, s->medeleg, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x303, s->mideleg, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x304, s->mie, s);  // mie & sie
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x305, s->mtvec, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x105, s->stvec, s);
    create_csr12_recovery(rom, &code_pos, 0x320, s->mcountinhibit, s);
    create_csr12_recovery(rom, &code_pos, 0x306, s->mcounteren, s);
    create_csr12_recovery(rom, &code_pos, 0x106, s->scounteren, s);

    // NB: restore addr before cfgs for fewer surprises!
    for (int i = 0; i < 16; ++i)
        create_csr64_recovery(rom, &code_pos, &data_pos, CSR_PMPADDR(i), s->csr_pmpaddr[i], s);
    for (int i = 0; i < 4; i += 2)
        create_csr64_recovery(rom, &code_pos, &data_pos, CSR_PMPCFG(i), s->csr_pmpcfg[i], s);

    create_csr64_recovery(rom, &code_pos, &data_pos, 0x340, s->mscratch, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x341, s->mepc, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x342, s->mcause, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x343, s->mtval, s);

    create_csr64_recovery(rom, &code_pos, &data_pos, 0x140, s->sscratch, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x141, s->sepc, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x142, s->scause, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x143, s->stval, s);

    create_csr64_recovery(rom, &code_pos, &data_pos, 0x344, s->mip, s); // mip & sip

    for (int i = 3; i < 32; i++) { // Not 1 and 2 which are used by create_...
      create_reg_recovery(rom, &code_pos, &data_pos, i, s->reg[i]);
    }

    // Recover CLINT (Close to the end of the recovery to avoid extra cycles)
    // TODO: One per hart (multicore/SMP)

    fprintf(dromajo_stderr, "clint hartid=%d timecmp=%" PRId64 " cycles (%" PRId64 ")\n",
	    (int)s->mhartid, s->timecmp, s->mcycle/RTC_FREQ_DIV);

    // Assuming 16 ratio between CPU and CLINT and that CPU is reset to zero
    create_io64_recovery( rom, &code_pos, &data_pos, clint_base_addr + 0x4000, s->timecmp);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0xb02, s->minstret, s);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0xb00, s->mcycle, s);

    create_io64_recovery( rom, &code_pos, &data_pos, clint_base_addr + 0xbff8, s->mcycle/RTC_FREQ_DIV);

    for (int i = 1; i < 3; i++) { // recover 1 and 2 now
      create_reg_recovery(rom, &code_pos, &data_pos, i, s->reg[i]);
    }

    rom[code_pos++] = create_csrrw(1, 0x7b2);
    create_csr64_recovery(rom, &code_pos, &data_pos, 0x180, s->satp, s);
    // last Thing because it changes addresses. Use dscratch register to remember reg 1
    rom[code_pos++] = create_csrrs(1, 0x7b2);

    // dret 0x7b200073
    rom[code_pos++] = 0x7b200073;

    if (sizeof rom / sizeof *rom <= data_pos || data_pos_start <= code_pos) {
        fprintf(dromajo_stderr, "ERROR: ROM is too small. ROM_SIZE should increase.  "
                "Current code_pos=%d data_pos=%d\n", code_pos, data_pos);
        exit(-6);
    }

    serialize_memory(rom, ROM_SIZE, file);
    if (s->machine->common.save_format > 0) {
        char *f_name = (char *)alloca(strlen(file)+32);
        sprintf(f_name, "%s.hex", file);

        dump_hex_memory(rom, ROM_SIZE, f_name);
    }
}

void riscv_cpu_serialize(RISCVCPUState *s, const char *dump_name, const uint64_t clint_base_addr)
{
    FILE *conf_fd = 0;
    size_t n = strlen(dump_name) + 64;
    char *conf_name = (char *)alloca(n);
    snprintf(conf_name, n, "%s.re_regs", dump_name);

    conf_fd = fopen(conf_name, "w");
    if (conf_fd == 0)
        err(-3, "opening %s for serialization", conf_name);

    fprintf(conf_fd, "# DROMAJO serialization file\n");

    fprintf(conf_fd, "pc:0x%llx\n", (long long)s->pc);

    for (int i = 1; i < 32; i++) {
        fprintf(conf_fd, "reg_x%d:%llx\n", i, (long long)s->reg[i]);
    }

#if LEN > 0
    for (int i = 0; i < 32; i++) {
        fprintf(conf_fd, "reg_f%d:%llx\n", i, (long long)s->fp_reg[i]);
    }
    fprintf(conf_fd, "fflags:%c\n", s->fflags);
    fprintf(conf_fd, "frm:%c\n", s->frm);
#endif

    const char *priv_str = "USHM";
    fprintf(conf_fd, "priv:%c\n", priv_str[s->priv]);
    fprintf(conf_fd, "insn_counter:%" PRIu64 "\n", s->insn_counter);

    fprintf(conf_fd, "pending_exception:%d\n", s->pending_exception);

    fprintf(conf_fd, "mstatus:%llx\n", (unsigned long long)s->mstatus);
    fprintf(conf_fd, "mtvec:%llx\n", (unsigned long long)s->mtvec);
    fprintf(conf_fd, "mscratch:%llx\n", (unsigned long long)s->mscratch);
    fprintf(conf_fd, "mepc:%llx\n", (unsigned long long)s->mepc);
    fprintf(conf_fd, "mcause:%llx\n", (unsigned long long)s->mcause);
    fprintf(conf_fd, "mtval:%llx\n", (unsigned long long)s->mtval);

    fprintf(conf_fd, "misa:%" PRIu32 "\n", s->misa);
    fprintf(conf_fd, "mie:%" PRIu32 "\n", s->mie);
    fprintf(conf_fd, "mip:%" PRIu32 "\n", s->mip);
    fprintf(conf_fd, "medeleg:%" PRIu32 "\n", s->medeleg);
    fprintf(conf_fd, "mideleg:%" PRIu32 "\n", s->mideleg);
    fprintf(conf_fd, "mcounteren:%" PRIu32 "\n", s->mcounteren);
    fprintf(conf_fd, "mcountinhibit:%" PRIu32 "\n", s->mcountinhibit);
    fprintf(conf_fd, "tselect:%" PRIu32 "\n", s->tselect);

    fprintf(conf_fd, "stvec:%llx\n", (unsigned long long)s->stvec);
    fprintf(conf_fd, "sscratch:%llx\n", (unsigned long long)s->sscratch);
    fprintf(conf_fd, "sepc:%llx\n", (unsigned long long)s->sepc);
    fprintf(conf_fd, "scause:%llx\n", (unsigned long long)s->scause);
    fprintf(conf_fd, "stval:%llx\n", (unsigned long long)s->stval);
    fprintf(conf_fd, "satp:%llx\n", (unsigned long long)s->satp);
    fprintf(conf_fd, "scounteren:%llx\n", (unsigned long long)s->scounteren);

    for (int i = 0; i < 4; i += 2)
        fprintf(conf_fd, "pmpcfg%d:%llx\n", i, (unsigned long long)s->csr_pmpcfg[i]);
    for (int i = 0; i < 16; ++i)
        fprintf(conf_fd, "pmpaddr%d:%llx\n", i, (unsigned long long)s->csr_pmpaddr[i]);

    PhysMemoryRange *boot_ram = 0;
    int main_ram_found = 0;

    for (int i = s->mem_map->n_phys_mem_range-1; i >= 0; --i) {
        PhysMemoryRange *pr = &s->mem_map->phys_mem_range[i];
        fprintf(conf_fd, "mrange%d:0x%llx 0x%llx %s\n", i,
                (long long)pr->addr, (long long)pr->size,
                pr->is_ram ? "ram" : "io");

        if (pr->is_ram && pr->addr == ROM_BASE_ADDR) {

            assert(!boot_ram);
            boot_ram = pr;

        } else if (pr->is_ram && pr->addr == s->machine->ram_base_addr) {

            assert(!main_ram_found);
            main_ram_found = 1;

            char *f_name = (char *)alloca(strlen(dump_name)+64);
            sprintf(f_name, "%s.mainram", dump_name);

            serialize_memory(pr->phys_mem, pr->size, f_name);

            if (s->machine->common.save_format > 0) {
                char *f_name_hex = (char *)alloca(strlen(dump_name)+96);
                sprintf(f_name_hex, "%s.mainram.hex", dump_name);

                dump_hex_memory(pr->phys_mem, pr->size, f_name_hex);
            }
        }
    }

    if (!boot_ram || !main_ram_found) {
        fprintf(dromajo_stderr, "ERROR: could not find boot and main ram???\n");
        exit(-3);
    }

    n = strlen(dump_name) + 64;
    char *f_name = (char *)alloca(n);
    snprintf(f_name, n, "%s.bootram", dump_name);

    if (s->priv != 3 || ROM_BASE_ADDR + ROM_SIZE < s->pc) {
        fprintf(dromajo_stderr, "NOTE: creating a new boot rom\n");
        create_boot_rom(s, f_name, clint_base_addr);
    } else if (BOOT_BASE_ADDR < s->pc) {
        fprintf(dromajo_stderr, "ERROR: could not checkpoint when running inside the ROM\n");
        exit(-4);
    } else if (s->pc == BOOT_BASE_ADDR && boot_ram) {
        fprintf(dromajo_stderr, "NOTE: using the default dromajo ROM\n");
        serialize_memory(boot_ram->phys_mem, boot_ram->size, f_name);
    } else {
        fprintf(dromajo_stderr, "ERROR: unexpected PC address 0x%llx\n", (long long)s->pc);
        exit(-4);
    }
}

void riscv_cpu_deserialize(RISCVCPUState *s, const char *dump_name)
{
    for (int i = s->mem_map->n_phys_mem_range - 1; i >= 0; --i) {
        PhysMemoryRange *pr = &s->mem_map->phys_mem_range[i];

        if (pr->is_ram && pr->addr == ROM_BASE_ADDR) {

            size_t n = strlen(dump_name) + 64;
            char *boot_name = (char *)alloca(n);
            snprintf(boot_name, n, "%s.bootram", dump_name);

            deserialize_memory(pr->phys_mem, pr->size, boot_name);

        } else if (pr->is_ram && pr->addr == s->machine->ram_base_addr) {

            size_t n = strlen(dump_name) + 64;
            char *main_name = (char *)alloca(n);
            snprintf(main_name, n, "%s.mainram", dump_name);

            deserialize_memory(pr->phys_mem, pr->size, main_name);
        }
    }
}
