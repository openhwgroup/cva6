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
#ifndef RISCV_CPU_H
#define RISCV_CPU_H

#include "riscv.h"
#include <stdbool.h>

#define ROM_SIZE       0x00001000
#define ROM_BASE_ADDR  0x00010000
#define BOOT_BASE_ADDR 0x00010000

// The default RAM base, can be relocated with config "memory_base_addr"
#define RAM_BASE_ADDR  0x80000000

#define KERNEL_OFFSET      0x200000

#ifndef FLEN
#define FLEN 64
#endif /* !FLEN */

#define DUMP_INVALID_MEM_ACCESS
#define DUMP_MMU_EXCEPTIONS
//#define DUMP_INTERRUPTS
#define DUMP_INVALID_CSR
//#define DUMP_ILLEGAL_INSTRUCTION
//#define DUMP_EXCEPTIONS
//#define DUMP_CSR
#define CONFIG_LOGFILE
#define CONFIG_SW_MANAGED_A_AND_D 1
#define CONFIG_ALLOW_MISALIGNED_ACCESS 0

#if FLEN > 0
#include "softfp.h"
#endif

#define __exception __attribute__((warn_unused_result))

typedef uint64_t target_ulong;
typedef int64_t target_long;
#define PR_target_ulong "016" PRIx64

/* FLEN is the floating point register width */
#if FLEN > 0
#if FLEN == 32
typedef uint32_t fp_uint;
#define F32_HIGH 0
#elif FLEN == 64
typedef uint64_t fp_uint;
#define F32_HIGH ((fp_uint)-1 << 32)
#define F64_HIGH 0
#elif FLEN == 128
typedef uint128_t fp_uint;
#define F32_HIGH ((fp_uint)-1 << 32)
#define F64_HIGH ((fp_uint)-1 << 64)
#else
#error unsupported FLEN
#endif
#endif

/* MLEN is the maximum memory access width */
#if 64 <= 32 && FLEN <= 32
#define MLEN 32
#elif 64 <= 64 && FLEN <= 64
#define MLEN 64
#else
#define MLEN 128
#endif

#if MLEN == 32
typedef uint32_t mem_uint_t;
#elif MLEN == 64
typedef uint64_t mem_uint_t;
#elif MLEN == 128
typedef uint128_t mem_uint_t;
#else
#unsupported MLEN
#endif

#define TLB_SIZE 256


#define PG_SHIFT 12
#define PG_MASK ((1 << PG_SHIFT) - 1)

#define ASID_BITS 0

#define SATP_MASK ((15ULL << 60) | (((1ULL << ASID_BITS) - 1) << 44) | ((1ULL << 44) - 1))

#ifndef MAX_TRIGGERS
#define MAX_TRIGGERS 1 // As of right now, one trigger register
#endif

/* HPM masks

   Follows Rocket here; the lower 8-bits are reserved in any
   HPM event selector to identify an "event-setid" i.e. with 8-bits we
   can define 256-possible event-sets.  An event-set can contain 56
   possible events, i.e. 64-8, where each bit represents the mask for
   a particular event in an event-set.

   Dromajo currently has 7 event-sets and not all 56-events are
   implemented for each set.
*/
#define HPM_EVENT_SETMASK	0x00000007
#define HPM_EVENT_EVENTMASK	0xffffff00

typedef struct {
    target_ulong vaddr;
    uintptr_t mem_addend;
} TLBEntry;

/* Control-flow summary information */
typedef enum {
    ctf_nop = 1,
    ctf_taken_jump,
    ctf_taken_branch,
    // Indirect jumps come in four variants depending on hits
    // NB: the order is important
    ctf_taken_jalr,
    ctf_taken_jalr_pop,
    ctf_taken_jalr_push,
    ctf_taken_jalr_pop_push,
} RISCVCTFInfo;

typedef struct RISCVCPUState {
    RISCVMachine *machine;
    target_ulong pc;
    target_ulong reg[32];
    /* Co-simulation sometimes need to see the value of a register
     * prior to the just excuted instruction. */
    target_ulong reg_prior[32];
    int most_recently_written_reg;

#if FLEN > 0
    fp_uint fp_reg[32];
    int most_recently_written_fp_reg;
    uint32_t fflags;
    uint8_t frm;
#endif

    uint8_t priv; /* see PRV_x */
    uint8_t fs; /* MSTATUS_FS value */

    uint64_t insn_counter; // Simulator internal
    uint64_t minstret; // RISCV CSR (updated when insn_counter increases)
    uint64_t mcycle;   // RISCV CSR (updated when insn_counter increases)
    BOOL     debug_mode;
    BOOL     stop_the_counter; // Set in debug mode only (cleared after ending Debug)

    BOOL power_down_flag; /* True when the core is idle awaiting
                           * interrupts, does NOT mean terminate
                           * simulation */
    BOOL terminate_simulation;
    int pending_exception; /* used during MMU exception handling */
    target_ulong pending_tval;

    /* CSRs */
    target_ulong mstatus;
    target_ulong mtvec;
    target_ulong mscratch;
    target_ulong mepc;
    target_ulong mcause;
    target_ulong mtval;
    target_ulong mvendorid; /* ro */
    target_ulong marchid; /* ro */
    target_ulong mimpid; /* ro */
    target_ulong mhartid; /* ro */
    uint32_t misa;
    uint32_t mie;
    uint32_t mip;
    uint32_t medeleg;
    uint32_t mideleg;
    uint32_t mcounteren;
    uint32_t mcountinhibit;
    uint32_t tselect;
    target_ulong tdata1[MAX_TRIGGERS];
    target_ulong tdata2[MAX_TRIGGERS];
    target_ulong tdata3[MAX_TRIGGERS];

    target_ulong mhpmevent[32];

    uint64_t csr_pmpcfg[4]; // But only 0 and 2 are valid
    uint64_t csr_pmpaddr[16];

    // pmpcfg and pmpadddr unpacked
    int pmp_n; // 0..pmp_n-1 entries are valid
    struct pmp_addr {
        uint64_t lo, hi; // [lo; hi)  NB: not inclusive
    } pmp[16];
    uint8_t pmpcfg[16];

    target_ulong stvec;
    target_ulong sscratch;
    target_ulong sepc;
    target_ulong scause;
    target_ulong stval;
    uint64_t satp; /* currently 64 bit physical addresses max */
    uint32_t scounteren;

    target_ulong dcsr; // Debug CSR 0x7b0 (debug spec only)
    target_ulong dpc;  // Debug DPC 0x7b1 (debug spec only)
    target_ulong dscratch;  // Debug dscratch 0x7b2 (debug spec only)

    uint32_t plic_enable_irq;

    target_ulong load_res; /* for atomic LR/SC */

    PhysMemoryMap *mem_map;
    int physical_addr_len;

    TLBEntry tlb_read[TLB_SIZE];
    TLBEntry tlb_write[TLB_SIZE];
    TLBEntry tlb_code[TLB_SIZE];
#ifndef PADDR_INLINE
    target_ulong tlb_read_paddr_addend[TLB_SIZE];
    target_ulong tlb_write_paddr_addend[TLB_SIZE];
    target_ulong tlb_code_paddr_addend[TLB_SIZE];
#endif

    // Benchmark return value
    uint64_t benchmark_exit_code;

    /* Control Flow Info */
    RISCVCTFInfo info;
    target_ulong next_addr; /* the CFI target address-- only valid for CFIs. */

    /* RTC */
    uint64_t timecmp;

    bool ignore_sbi_shutdown;

    /* Extension state, not used by Dromajo itself */
    void *ext_cpu_state;
} RISCVCPUState;

RISCVCPUState *riscv_cpu_init(RISCVMachine *machine, int hartid);
void riscv_cpu_end(RISCVCPUState *s);
int riscv_cpu_interp(RISCVCPUState *s, int n_cycles);
uint64_t riscv_cpu_get_cycles(RISCVCPUState *s);
void riscv_cpu_set_mip(RISCVCPUState *s, uint32_t mask);
void riscv_cpu_reset_mip(RISCVCPUState *s, uint32_t mask);
uint32_t riscv_cpu_get_mip(RISCVCPUState *s);
BOOL riscv_cpu_get_power_down(RISCVCPUState *s);
uint32_t riscv_cpu_get_misa(RISCVCPUState *s);
void riscv_cpu_flush_tlb_write_range_ram(RISCVCPUState *s,
                                         uint8_t *ram_ptr, size_t ram_size);
void riscv_set_pc(RISCVCPUState *s, uint64_t pc);
uint64_t riscv_get_pc(RISCVCPUState *s);
uint64_t riscv_get_reg(RISCVCPUState *s, int rn);
uint64_t riscv_get_reg_previous(RISCVCPUState *s, int rn);
uint64_t riscv_get_fpreg(RISCVCPUState *s, int rn);
void riscv_set_reg(RISCVCPUState *s, int rn, uint64_t val);
void riscv_dump_regs(RISCVCPUState *s);
int riscv_read_insn(RISCVCPUState *s, uint32_t *insn, uint64_t addr);
void riscv_repair_csr(RISCVCPUState *s, uint32_t reg_num, uint64_t csr_num,
                      uint64_t csr_val);
void riscv_cpu_sync_regs(RISCVCPUState *s);
int riscv_get_priv_level(RISCVCPUState *s);
int riscv_get_most_recently_written_reg(RISCVCPUState *s);
int riscv_get_most_recently_written_fp_reg(RISCVCPUState *s);
void riscv_get_ctf_info(RISCVCPUState *s, RISCVCTFInfo *info);
void riscv_get_ctf_target(RISCVCPUState *s, uint64_t *target);

int riscv_cpu_interp64(RISCVCPUState *s, int n_cycles);
BOOL riscv_terminated(RISCVCPUState *s);
void riscv_set_debug_mode(RISCVCPUState *s, bool on);

int riscv_benchmark_exit_code(RISCVCPUState *s);

#include "riscv_machine.h"
void riscv_cpu_serialize(RISCVCPUState *s, const char *dump_name, const uint64_t clint_base_addr);
void riscv_cpu_deserialize(RISCVCPUState *s, const char *dump_name);

int riscv_cpu_read_memory(RISCVCPUState *s, mem_uint_t *pval, target_ulong addr, int size_log2);
int riscv_cpu_write_memory(RISCVCPUState *s, target_ulong addr, mem_uint_t val, int size_log2);

#define PHYS_MEM_READ_WRITE(size, uint_type) \
  void      riscv_phys_write_u ## size(RISCVCPUState *, target_ulong, uint_type, bool *); \
  uint_type riscv_phys_read_u  ## size(RISCVCPUState *, target_ulong, bool *);

PHYS_MEM_READ_WRITE(8, uint8_t)
PHYS_MEM_READ_WRITE(32, uint32_t)
PHYS_MEM_READ_WRITE(64, uint64_t)

#undef PHYS_MEM_READ_WRITE

typedef enum {
    ACCESS_READ,
    ACCESS_WRITE,
    ACCESS_CODE,
} riscv_memory_access_t;

int riscv_cpu_get_phys_addr(RISCVCPUState *s,
                            target_ulong vaddr,
                            riscv_memory_access_t access,
                            target_ulong *ppaddr);

uint64_t riscv_cpu_get_mstatus(RISCVCPUState* s);

bool riscv_cpu_pmp_access_ok(RISCVCPUState *s,
                             uint64_t paddr,
                             size_t size,
                             pmpcfg_t perm);
#endif
