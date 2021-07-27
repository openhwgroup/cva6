/*
 * RISC-V definitions
 *
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
 * Implementation independent ISA definitions -- most of this comes
 * straight from the specifications.
 */

#ifndef RISCV_H
#define RISCV_H

#define MIP_USIP (1 << 0)
#define MIP_SSIP (1 << 1)
//#define MIP_HSIP (1 << 2)  Removed in Priv 1.11 (draft)
#define MIP_MSIP (1 << 3)
#define MIP_UTIP (1 << 4)
#define MIP_STIP (1 << 5)
//#define MIP_HTIP (1 << 6)  Removed in Priv 1.11 (draft)
#define MIP_MTIP (1 << 7)
#define MIP_UEIP (1 << 8)
#define MIP_SEIP (1 << 9)
//#define MIP_HEIP (1 << 10)  Removed in Priv 1.11 (draft)
#define MIP_MEIP (1 << 11)
// ET-specific, non-standard counter overflow interrupts.
//#define MIP_UCIP (1 << 16) probably not necessary.
//#define MIP_SCIP (1 << 17) probably not necessary.
#define MIP_MCIP (1 << 18)

#define MIE_USIE MIP_USIP
#define MIE_SSIE MIP_SSIP
#define MIE_MSIE MIP_MSIP
#define MIE_UTIE MIP_UTIP
#define MIE_STIE MIP_STIP
#define MIE_MTIE MIP_MTIP
#define MIE_UEIE MIP_UEIP
#define MIE_SEIE MIP_SEIP
#define MIE_MEIE MIP_MEIP
#define MIE_MCIP MIP_MCIP


#define CAUSE_MISALIGNED_FETCH    0x0
#define CAUSE_FAULT_FETCH         0x1
#define CAUSE_ILLEGAL_INSTRUCTION 0x2
#define CAUSE_BREAKPOINT          0x3
#define CAUSE_MISALIGNED_LOAD     0x4
#define CAUSE_FAULT_LOAD          0x5
#define CAUSE_MISALIGNED_STORE    0x6
#define CAUSE_FAULT_STORE         0x7
#define CAUSE_USER_ECALL          0x8
#define CAUSE_SUPERVISOR_ECALL    0x9
#define CAUSE_HYPERVISOR_ECALL    0xa
#define CAUSE_MACHINE_ECALL       0xb
#define CAUSE_FETCH_PAGE_FAULT    0xc
#define CAUSE_LOAD_PAGE_FAULT     0xd
#define CAUSE_STORE_PAGE_FAULT    0xf

#define SCAUSE_MASK     0x800000000000001full // 5 writable bits+MSB
#define MCAUSE_MASK     0x80000000000000ffull // 8 writable bits+MSB
#define CAUSE_INTERRUPT 0x8000000000000000ull

#define PRV_U 0
#define PRV_S 1
#define PRV_H 2
#define PRV_M 3

/* misa CSR */
#define MCPUID_SUPER   (1 << ('S' - 'A'))
#define MCPUID_USER    (1 << ('U' - 'A'))
#define MCPUID_I       (1 << ('I' - 'A'))
#define MCPUID_M       (1 << ('M' - 'A'))
#define MCPUID_A       (1 << ('A' - 'A'))
#define MCPUID_F       (1 << ('F' - 'A'))
#define MCPUID_D       (1 << ('D' - 'A'))
#define MCPUID_Q       (1 << ('Q' - 'A'))
#define MCPUID_C       (1 << ('C' - 'A'))
#define MCPUID_X       (1 << ('X' - 'A'))

/* mstatus CSR */

#define MSTATUS_SPIE_SHIFT 5
#define MSTATUS_MPIE_SHIFT 7
#define MSTATUS_SPP_SHIFT 8
#define MSTATUS_MPP_SHIFT 11
#define MSTATUS_FS_SHIFT 13
#define MSTATUS_UXL_SHIFT 32
#define MSTATUS_SXL_SHIFT 34

#define MSTATUS_UIE (1 << 0)
#define MSTATUS_SIE (1 << 1)
#define MSTATUS_HIE (1 << 2)
#define MSTATUS_MIE (1 << 3)
#define MSTATUS_UPIE (1 << 4)
#define MSTATUS_SPIE (1 << MSTATUS_SPIE_SHIFT)
#define MSTATUS_HPIE (1 << 6)
#define MSTATUS_MPIE (1 << MSTATUS_MPIE_SHIFT)
#define MSTATUS_SPP (1 << MSTATUS_SPP_SHIFT)
#define MSTATUS_HPP (3 << 9)
#define MSTATUS_MPP (3 << MSTATUS_MPP_SHIFT)
#define MSTATUS_FS (3 << MSTATUS_FS_SHIFT)
#define MSTATUS_XS (3 << 15)
#define MSTATUS_MPRV (1 << 17)
#define MSTATUS_SUM (1 << 18)
#define MSTATUS_MXR (1 << 19)
#define MSTATUS_TVM (1 << 20)
#define MSTATUS_TW (1 << 21)
#define MSTATUS_TSR (1 << 22)
#define MSTATUS_UXL_MASK ((uint64_t)3 << MSTATUS_UXL_SHIFT)
#define MSTATUS_SXL_MASK ((uint64_t)3 << MSTATUS_SXL_SHIFT)

// A few of Debug Trigger Match Control bits (there are many more)
#define MCONTROL_M         (1 << 6)
#define MCONTROL_S         (1 << 4)
#define MCONTROL_U         (1 << 3)
#define MCONTROL_EXECUTE   (1 << 2)
#define MCONTROL_STORE     (1 << 1)
#define MCONTROL_LOAD      (1 << 0)

#define PHYSICAL_ADDR_LEN_DEFAULT               40

/* SBI calls */
typedef enum {
    SBI_SET_TIMER,
    SBI_CONSOLE_PUTCHAR,
    SBI_CONSOLE_GETCHAR,
    SBI_CLEAR_IPI,
    SBI_SEND_IPI,
    SBI_REMOTE_FENCE_I,
    SBI_REMOTE_SFENCE_VMA,
    SBI_REMOTE_SFENCE_VMA_ASID,
    SBI_SHUTDOWN,
    SBI_DISK_READ,
    SBI_DISK_WRITE,
    SBI_DISK_SIZE,
} sbi_call_t;

/* PMP */

#define CSR_PMPCFG(n)                           (0x3A0 + (n)) // n = 0 or 2
#define CSR_PMPADDR(n)                          (0x3B0 + (n)) // n = 0..15

#define PMP_N           8 // Spec defines 16, we implement 8

typedef enum {
    PMPCFG_R       =    1, // NB: the three bottom bits follow the standard permissions order
    PMPCFG_W       =    2,
    PMPCFG_X       =    4,
    PMPCFG_A_MASK  = 0x18,
    PMPCFG_A_OFF   =    0,
    PMPCFG_A_TOR   =    8,
    PMPCFG_A_NA4   = 0x10,
    PMPCFG_A_NAPOT = 0x18,
    PMPCFG_RES     = 0x60,
    PMPCFG_L       = 0x80,
} pmpcfg_t;

/* Copy & paste from qemu include/hw/riscv/virt.h */
#define PLIC_HART_CONFIG      "MS"
#define PLIC_NUM_SOURCES           127
#define PLIC_NUM_PRIORITIES          7
#define PLIC_PRIORITY_BASE           4
#define PLIC_PENDING_BASE       0x1000
#define PLIC_ENABLE_BASE        0x2000
#define PLIC_ENABLE_STRIDE        0x80
#define PLIC_CONTEXT_BASE     0x200000
#define PLIC_CONTEXT_STRIDE     0x1000

#define PLIC_BITFIELD_WORDS ((PLIC_NUM_SOURCES + 31) >> 5)

#endif
