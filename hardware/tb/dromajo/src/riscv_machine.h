/*
 * RISCV machine
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
#ifndef RISCV_MACHINE_H
#define RISCV_MACHINE_H

#include "virtio.h"
#include "machine.h"
#include "riscv_cpu.h"

#ifdef LIVECACHE
#include "LiveCacheCore.h"
#endif

#define MAX_CPUS  8

/* Hooks */
typedef struct RISCVMachineHooks {
    /* Returns -1 if invalid CSR, 0 if OK. */
    int (*csr_read) (RISCVCPUState *s, uint32_t csr, uint64_t *pval);
    int (*csr_write)(RISCVCPUState *s, uint32_t csr, uint64_t   val);
} RISCVMachineHooks;

struct RISCVMachine {
    VirtMachine common;
    RISCVMachineHooks hooks;
    PhysMemoryMap *mem_map;
#ifdef LIVECACHE
    LiveCache *llc;
#endif
    RISCVCPUState *cpu_state[MAX_CPUS];
    int      ncpus;
    uint64_t ram_size;
    uint64_t ram_base_addr;
    /* PLIC */
    uint32_t plic_pending_irq;
    uint32_t plic_served_irq;
    IRQSignal plic_irq[32]; /* IRQ 0 is not used */

    /* HTIF */
    uint64_t htif_tohost_addr;

    VIRTIODevice *keyboard_dev;
    VIRTIODevice *mouse_dev;

    int virtio_count;

    /* MMIO range (for co-simulation only) */
    uint64_t mmio_start;
    uint64_t mmio_end;
    AddressSet *mmio_addrset;
    uint64_t mmio_addrset_size;

    /* Reset vector */
    uint64_t reset_vector;

    /* Bootrom Params */
    bool compact_bootrom;

    /* PLIC/CLINT Params */
    uint64_t plic_base_addr;
    uint64_t plic_size;
    uint64_t clint_base_addr;
    uint64_t clint_size;

    /* Append to misa custom extensions */
    bool custom_extension;

    /* Extension state, not used by Dromajo itself */
    void *ext_state;

    /* Core specific configs */
    uint64_t* missing_csrs;
    uint64_t missing_csrs_size;
    uint64_t* skip_commit;
    uint64_t skip_commit_size;
};

#define PLIC_BASE_ADDR  0x10000000
#define PLIC_SIZE        0x2000000

#define CLINT_BASE_ADDR 0x02000000
#define CLINT_SIZE      0x000c0000

#define RTC_FREQ_DIV 16 /* arbitrary, relative to CPU freq to have a
                           10 MHz frequency */

#define HTIF_BASE_ADDR          0x40008000
#define IDE_BASE_ADDR           0x40009000
#define VIRTIO_BASE_ADDR        0x40010000
#define VIRTIO_SIZE                 0x1000
#define VIRTIO_IRQ                       1
#define FRAMEBUFFER_BASE_ADDR   0x41000000

// sifive,uart, same as qemu UART0 (qemu has 2 sifive uarts)
#define UART0_BASE_ADDR         0x54000000
#define UART0_SIZE                      32
#define UART0_IRQ                        3

#define RTC_FREQ                  10000000

#endif
