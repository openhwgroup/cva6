/*
 * RISCV machine
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
#include <errno.h>
#include <unistd.h>
#include <time.h>

#include "cutils.h"
#include "iomem.h"
#include "riscv_machine.h"
#include "dw_apb_uart.h"
#include "elf64.h"

/* RISCV machine */

//#define DUMP_UART
//#define DUMP_CLINT
//#define DUMP_HTIF
//#define DUMP_PLIC
#define DUMP_DTB

#define USE_SIFIVE_UART

enum {
    SIFIVE_UART_TXFIFO        = 0,
    SIFIVE_UART_RXFIFO        = 4,
    SIFIVE_UART_TXCTRL        = 8,
    SIFIVE_UART_TXMARK        = 10,
    SIFIVE_UART_RXCTRL        = 12,
    SIFIVE_UART_RXMARK        = 14,
    SIFIVE_UART_IE            = 16,
    SIFIVE_UART_IP            = 20,
    SIFIVE_UART_DIV           = 24,
    SIFIVE_UART_MAX           = 32
};

enum {
    SIFIVE_UART_IE_TXWM       = 1, /* Transmit watermark interrupt enable */
    SIFIVE_UART_IE_RXWM       = 2  /* Receive watermark interrupt enable */
};

enum {
    SIFIVE_UART_IP_TXWM       = 1, /* Transmit watermark interrupt pending */
    SIFIVE_UART_IP_RXWM       = 2  /* Receive watermark interrupt pending */
};

static uint64_t rtc_get_time(RISCVMachine *m)
{
    return m->cpu_state[0]->mcycle / RTC_FREQ_DIV;
}

typedef struct SiFiveUARTState {
    CharacterDevice *cs; // Console
    uint32_t irq;
    uint8_t rx_fifo[8];
    unsigned int rx_fifo_len;
    uint32_t ie;
    uint32_t ip;
    uint32_t txctrl;
    uint32_t rxctrl;
    uint32_t div;
} SiFiveUARTState;

static void uart_update_irq(SiFiveUARTState *s)
{
    int cond = 0;
    if ((s->ie & SIFIVE_UART_IE_RXWM) && s->rx_fifo_len) {
        cond = 1;
    }
    if (cond) {
        fprintf(dromajo_stderr, "uart_update_irq: FIXME we should raise IRQ saying that there is new data\n");
    }
}

static uint32_t mmio_read(void *opaque, uint32_t offset, int size_log2)
{
    fprintf(dromajo_stderr, "mmio_read: offset=%x size_log2=%d\n", offset, size_log2);

    return 0;
}

static void mmio_write(void *opaque, uint32_t offset, uint32_t val, int size_log2)
{
    fprintf(dromajo_stderr, "mmio_write: offset=%x size_log2=%d val=%x\n", offset, size_log2, val);
}

static uint32_t uart_read(void *opaque, uint32_t offset, int size_log2)
{
    SiFiveUARTState *s = (SiFiveUARTState *)opaque;

#ifdef DUMP_UART
    fprintf(dromajo_stderr, "uart_read: offset=%x size_log2=%d\n", offset, size_log2);
#endif
    switch (offset) {
    case SIFIVE_UART_RXFIFO: {
        CharacterDevice *cs = s->cs;
        unsigned char r;
        int ret = cs->read_data(cs->opaque, &r, 1);
        if (ret) {
#ifdef DUMP_UART
            fprintf(dromajo_stderr, "uart_read: val=%x\n", r);
#endif
            return r;
        }
        return 0x80000000;
    }
    case SIFIVE_UART_TXFIFO:
        return 0; /* Should check tx fifo */
    case SIFIVE_UART_IE:
        return s->ie;
    case SIFIVE_UART_IP:
        return s->rx_fifo_len ? SIFIVE_UART_IP_RXWM : 0;
    case SIFIVE_UART_TXCTRL:
        return s->txctrl;
    case SIFIVE_UART_RXCTRL:
        return s->rxctrl;
    case SIFIVE_UART_DIV:
        return s->div;
    }

    fprintf(dromajo_stderr, "%s: bad read: offset=0x%x\n", __func__, (int)offset);
    return 0;
}

static void uart_write(void *opaque, uint32_t offset, uint32_t val, int size_log2)
{
    SiFiveUARTState *s = (SiFiveUARTState *)opaque;
    CharacterDevice *cs = s->cs;
    unsigned char ch = val;

#ifdef DUMP_UART
    fprintf(dromajo_stderr, "uart_write: offset=%x val=%x size_log2=%d\n", offset, val, size_log2);
#endif

    switch (offset) {
    case SIFIVE_UART_TXFIFO:
        cs->write_data(cs->opaque, &ch, 1);
        return;
    case SIFIVE_UART_IE:
        s->ie = val;
        uart_update_irq(s);
        return;
    case SIFIVE_UART_TXCTRL:
        s->txctrl = val;
        return;
    case SIFIVE_UART_RXCTRL:
        s->rxctrl = val;
        return;
    case SIFIVE_UART_DIV:
        s->div = val;
        return;
    }

    fprintf(dromajo_stderr, "%s: bad write: addr=0x%x v=0x%x\n", __func__, (int)offset, (int)val);
}

/* CLINT registers
 * 0000 msip hart 0
 * 0004 msip hart 1
 * 4000 mtimecmp hart 0 lo
 * 4004 mtimecmp hart 0 hi
 * 4008 mtimecmp hart 1 lo
 * 400c mtimecmp hart 1 hi
 * bff8 mtime lo
 * bffc mtime hi
 */

static uint32_t clint_read(void *opaque, uint32_t offset, int size_log2)
{
    RISCVMachine *m = (RISCVMachine *)opaque;
    uint32_t val;

    if (0 <= offset && offset < 0x4000) {
        int hartid = offset >> 2;
        if (m->ncpus <= hartid) {
            fprintf(stderr, "%s: MSIP access for hartid:%d which is beyond ncpus\n", __func__, hartid);
            val = 0;
        } else {
            val = (riscv_cpu_get_mip(m->cpu_state[hartid]) & MIP_MSIP) != 0;
        }
    } else if (offset == 0xbff8) {
        uint64_t mtime = m->cpu_state[0]->mcycle / RTC_FREQ_DIV; // WARNING: mcycle may need to move to RISCVMachine
        val = mtime;
    } else if (offset == 0xbffc) {
        uint64_t mtime = m->cpu_state[0]->mcycle / RTC_FREQ_DIV;
        val = mtime >> 32;
    } else if (0x4000 <= offset && offset < 0xbff8) {
        int hartid = (offset - 0x4000) >> 3;
        if (m->ncpus <= hartid) {
            fprintf(stderr, "%s: MSIP access for hartid:%d which is beyond ncpus\n", __func__, hartid);
            val = 0;
        } else if ((offset >> 2) & 1) {
            val = m->cpu_state[hartid]->timecmp >> 32;
        } else {
            val = m->cpu_state[hartid]->timecmp;
        }
    } else {
        fprintf(stderr, "clint_read to unmanaged address CLINT_BASE+0x%x\n", offset);
        val = 0;
    }

#ifdef DUMP_CLINT
    fprintf(dromajo_stderr, "clint_read: offset=%x val=%x\n", offset, val);
#endif

    switch (size_log2) {
        case 1:
            val = val & 0xffff;
            break;
        case 2:
            val = val & 0xffffffff;
            break;
        case 3:
        default:
            break;
    }

    return val;
}

static void clint_write(void *opaque, uint32_t offset, uint32_t val,
                        int size_log2)
{
    RISCVMachine *m = (RISCVMachine *)opaque;

    switch (size_log2) {
        case 1:
            val = val & 0xffff;
            break;
        case 2:
            val = val & 0xffffffff;
            break;
        case 3:
        default:
            break;
    }

    if (0 <= offset && offset < 0x4000) {
        int hartid = offset >> 2;
        if (m->ncpus <= hartid) {
            fprintf(stderr, "%s: MSIP access for hartid:%d which is beyond ncpus\n", __func__, hartid);
        } else if (val & 1)
            riscv_cpu_set_mip(m->cpu_state[hartid], MIP_MSIP);
        else
            riscv_cpu_reset_mip(m->cpu_state[hartid], MIP_MSIP);
    } else if (offset == 0xbff8) {
        uint64_t mtime = m->cpu_state[0]->mcycle / RTC_FREQ_DIV; // WARNING: move mcycle to RISCVMachine
        mtime = (mtime & 0xFFFFFFFF00000000L) + val;
        m->cpu_state[0]->mcycle = mtime * RTC_FREQ_DIV;
    } else if (offset == 0xbffc) {
        uint64_t mtime = m->cpu_state[0]->mcycle / RTC_FREQ_DIV;
        mtime = (mtime & 0x00000000FFFFFFFFL) + ((uint64_t)val << 32);
        m->cpu_state[0]->mcycle = mtime * RTC_FREQ_DIV;
    } else if (0x4000 <= offset && offset < 0xbff8) {
        int hartid = (offset - 0x4000) >> 3;
        if (m->ncpus <= hartid) {
            fprintf(stderr, "%s: MSIP access for hartid:%d which is beyond ncpus\n", __func__, hartid);
        } else if ((offset >> 2) & 1) {
            m->cpu_state[hartid]->timecmp = (m->cpu_state[hartid]->timecmp & 0xffffffff) | ((uint64_t)val << 32);
            riscv_cpu_reset_mip(m->cpu_state[hartid], MIP_MTIP);
        } else {
            m->cpu_state[hartid]->timecmp = (m->cpu_state[hartid]->timecmp & ~0xffffffff) | val;
            riscv_cpu_reset_mip(m->cpu_state[hartid], MIP_MTIP);
        }
    } else {
        fprintf(stderr, "clint_write to unmanaged address CLINT_BASE+0x%x\n", offset);
        val = 0;
    }

#ifdef DUMP_CLINT
    fprintf(dromajo_stderr, "clint_write: offset=%x val=%x\n", offset, val);
#endif
}

static void plic_update_mip(RISCVMachine *s, int hartid)
{
    uint32_t mask = s->plic_pending_irq & ~s->plic_served_irq;
    RISCVCPUState *cpu = s->cpu_state[hartid];
    if (mask) {
        riscv_cpu_set_mip(cpu, MIP_MEIP | MIP_SEIP);
    } else {
        riscv_cpu_reset_mip(cpu, MIP_MEIP | MIP_SEIP);
    }
}

static uint32_t plic_priority[PLIC_NUM_SOURCES + 1]; // XXX migrate to VirtMachine!

static uint32_t plic_read(void *opaque, uint32_t offset, int size_log2)
{
    uint32_t val = 0;
    RISCVMachine *s = (RISCVMachine *)opaque;

    assert(size_log2 == 2);
    if (PLIC_PRIORITY_BASE <= offset && offset < PLIC_PRIORITY_BASE + (PLIC_NUM_SOURCES << 2)) {
        uint32_t irq = ((offset - PLIC_PRIORITY_BASE) >> 2) + 1;
        assert(irq < PLIC_NUM_SOURCES);
        val = plic_priority[irq];
    } else if (PLIC_PENDING_BASE <= offset && offset < PLIC_PENDING_BASE + (PLIC_NUM_SOURCES >> 3)) {
        if (offset == PLIC_PENDING_BASE)
            val = s->plic_pending_irq;
        else
            val = 0;
    } else if (PLIC_ENABLE_BASE <= offset && offset < PLIC_ENABLE_BASE + (PLIC_ENABLE_STRIDE * MAX_CPUS)) {
        int addrid = (offset - PLIC_ENABLE_BASE) / PLIC_ENABLE_STRIDE;
        int hartid = addrid / 2; // PLIC_HART_CONFIG is "MS"
        if (hartid <= s->ncpus) {
            //uint32_t wordid = (offset & (PLIC_ENABLE_STRIDE-1))>>2;
            RISCVCPUState *cpu = s->cpu_state[hartid];
            val = cpu->plic_enable_irq;
        } else {
            val = 0;
        }
    } else if (PLIC_CONTEXT_BASE <= offset && offset < PLIC_CONTEXT_BASE + PLIC_CONTEXT_STRIDE * MAX_CPUS) {
        uint32_t hartid = (offset - PLIC_CONTEXT_BASE) / PLIC_CONTEXT_STRIDE;
        uint32_t wordid = (offset & (PLIC_CONTEXT_STRIDE - 1)) >> 2;
        if (wordid == 0) {
            val = 0; // target_priority in qemu
        } else if (wordid == 4) {
            uint32_t mask = s->plic_pending_irq & ~s->plic_served_irq;
            if (mask != 0) {
                int i = ctz32(mask);
                s->plic_served_irq |= 1 << i;
                plic_update_mip(s, hartid);
                val = i + 1;
            } else {
                val = 0;
            }
        }
    } else {
        fprintf(stderr, "plic_read: unknown offset=%x\n", offset);
        val = 0;
    }
#ifdef DUMP_PLIC
    fprintf(dromajo_stderr, "plic_read: offset=%x val=%x\n", offset, val);
#endif

    return val;
}

static void plic_write(void *opaque, uint32_t offset, uint32_t val, int size_log2)
{
    RISCVMachine *s = (RISCVMachine *)opaque;

    assert(size_log2 == 2);
    if (PLIC_PRIORITY_BASE <= offset && offset < PLIC_PRIORITY_BASE + (PLIC_NUM_SOURCES << 2)) {
        uint32_t irq = ((offset - PLIC_PRIORITY_BASE) >> 2) + 1;
        assert(irq < PLIC_NUM_SOURCES);
        plic_priority[irq] = val & 7;

    } else if (PLIC_PENDING_BASE <= offset && offset < PLIC_PENDING_BASE + (PLIC_NUM_SOURCES >> 3)) {
        fprintf(stderr, "plic_write: INVALID pending write to offset=0x%x\n", offset);
    } else if (PLIC_ENABLE_BASE <= offset && offset < PLIC_ENABLE_BASE + PLIC_ENABLE_STRIDE * MAX_CPUS) {
        int addrid = (offset - PLIC_ENABLE_BASE) / PLIC_ENABLE_STRIDE;
        int hartid = addrid / 2; // PLIC_HART_CONFIG is "MS"
        if (hartid <= s->ncpus) {
            //uint32_t wordid = (offset & (PLIC_ENABLE_STRIDE - 1)) >> 2;
            RISCVCPUState *cpu = s->cpu_state[hartid];
            cpu->plic_enable_irq = val;
        }
    } else if (PLIC_CONTEXT_BASE <= offset && offset < PLIC_CONTEXT_BASE + PLIC_CONTEXT_STRIDE * MAX_CPUS) {
        uint32_t hartid = (offset - PLIC_CONTEXT_BASE) / PLIC_CONTEXT_STRIDE;
        uint32_t wordid = (offset & (PLIC_CONTEXT_STRIDE - 1)) >> 2;
        if (wordid == 0) {
            plic_priority[wordid] = val;
        } else if (wordid == 4) {
            int irq = val & 31;
            fprintf(stderr, "plic_write: hartid=%d claim wordid=%d offset=%x val=%x irq=%d\n",
                    hartid, wordid, offset, val, irq);
            uint32_t mask = 1 << (irq - 1);
            s->plic_served_irq &= ~mask;
        } else {
            fprintf(stderr, "plic_write: hartid=%d ERROR?? unexpected wordid=%d offset=%x val=%x\n",
                    hartid, wordid, offset, val);
        }
    } else {
        fprintf(stderr, "plic_write: ERROR: unexpected offset=%x val=%x\n", offset, val);
    }
#ifdef DUMP_PLIC
    fprintf(dromajo_stderr, "plic_write: offset=%x val=%x\n", offset, val);
#endif
}

static void plic_set_irq(void *opaque, int irq_num, int state)
{
    RISCVMachine *m = (RISCVMachine *)opaque;

    uint32_t mask = 1 << (irq_num - 1);

    if (state)
        m->plic_pending_irq |= mask;
    else
        m->plic_pending_irq &= ~mask;

    for (int hartid = 0; hartid < m->ncpus; ++hartid) {
        plic_update_mip(m, hartid);
    }
}

static uint8_t *get_ram_ptr(RISCVMachine *s, uint64_t paddr)
{
    PhysMemoryRange *pr = get_phys_mem_range(s->mem_map, paddr);
    if (!pr || !pr->is_ram)
        return NULL;
    return pr->phys_mem + (uintptr_t)(paddr - pr->addr);
}

/* FDT machine description */

#define FDT_MAGIC       0xd00dfeed
#define FDT_VERSION     17

struct fdt_header {
    uint32_t magic;
    uint32_t totalsize;
    uint32_t off_dt_struct;
    uint32_t off_dt_strings;
    uint32_t off_mem_rsvmap;
    uint32_t version;
    uint32_t last_comp_version; /* <= 17 */
    uint32_t boot_cpuid_phys;
    uint32_t size_dt_strings;
    uint32_t size_dt_struct;
};

struct fdt_reserve_entry {
    uint64_t address;
    uint64_t size;
};

#define FDT_BEGIN_NODE  1
#define FDT_END_NODE    2
#define FDT_PROP        3
#define FDT_NOP         4
#define FDT_END         9

typedef struct {
    uint32_t *tab;
    int tab_len;
    int tab_size;
    int open_node_count;

    char *string_table;
    int string_table_len;
    int string_table_size;
} FDTState;

static FDTState *fdt_init(void)
{
    FDTState *s = (FDTState *)mallocz(sizeof *s);
    return s;
}

static void fdt_alloc_len(FDTState *s, int len)
{
    if (unlikely(len > s->tab_size)) {
        int new_size = max_int(len, s->tab_size * 3 / 2);
        s->tab = (uint32_t *)realloc(s->tab, new_size * sizeof(uint32_t));
        s->tab_size = new_size;
    }
}

static void fdt_put32(FDTState *s, int v)
{
    fdt_alloc_len(s, s->tab_len + 1);
    s->tab[s->tab_len++] = cpu_to_be32(v);
}

/* the data is zero padded */
static void fdt_put_data(FDTState *s, const uint8_t *data, int len)
{
    int len1 = (len + 3) / 4;
    fdt_alloc_len(s, s->tab_len + len1);
    memcpy(s->tab + s->tab_len, data, len);
    memset((uint8_t *)(s->tab + s->tab_len) + len, 0, -len & 3);
    s->tab_len += len1;
}

static void fdt_begin_node(FDTState *s, const char *name)
{
    fdt_put32(s, FDT_BEGIN_NODE);
    fdt_put_data(s, (const uint8_t *)name, strlen(name) + 1);
    s->open_node_count++;
}

static void fdt_begin_node_num(FDTState *s, const char *name, uint64_t n)
{
    char buf[256];
    snprintf(buf, sizeof(buf), "%s@%" PRIx64, name, n);
    fdt_begin_node(s, buf);
}

static void fdt_end_node(FDTState *s)
{
    fdt_put32(s, FDT_END_NODE);
    s->open_node_count--;
}

static int fdt_get_string_offset(FDTState *s, const char *name)
{
    int pos, new_size, name_size, new_len;

    pos = 0;
    while (pos < s->string_table_len) {
        if (!strcmp(s->string_table + pos, name))
            return pos;
        pos += strlen(s->string_table + pos) + 1;
    }
    /* add a new string */
    name_size = strlen(name) + 1;
    new_len = s->string_table_len + name_size;
    if (new_len > s->string_table_size) {
        new_size = max_int(new_len, s->string_table_size * 3 / 2);
        s->string_table = (char *)realloc(s->string_table, new_size);
        s->string_table_size = new_size;
    }
    pos = s->string_table_len;
    memcpy(s->string_table + pos, name, name_size);
    s->string_table_len = new_len;
    return pos;
}

static void fdt_prop(FDTState *s, const char *prop_name,
                     const char *data, int data_len)
{
    fdt_put32(s, FDT_PROP);
    fdt_put32(s, data_len);
    fdt_put32(s, fdt_get_string_offset(s, prop_name));
    fdt_put_data(s, (const uint8_t *)data, data_len);
}

static void fdt_prop_tab_u32(FDTState *s, const char *prop_name,
                             uint32_t *tab, int tab_len)
{
    int i;
    fdt_put32(s, FDT_PROP);
    fdt_put32(s, tab_len * sizeof(uint32_t));
    fdt_put32(s, fdt_get_string_offset(s, prop_name));
    for (i = 0; i < tab_len; i++)
        fdt_put32(s, tab[i]);
}

static void fdt_prop_u32(FDTState *s, const char *prop_name, uint32_t val)
{
    fdt_prop_tab_u32(s, prop_name, &val, 1);
}

static void fdt_prop_u64(FDTState *s, const char *prop_name, uint64_t val)
{
    uint32_t tab[2];
    tab[0] = val >> 32;
    tab[1] = val;
    fdt_prop_tab_u32(s, prop_name, tab, 2);
}

static void fdt_prop_tab_u64_2(FDTState *s, const char *prop_name,
                               uint64_t v0, uint64_t v1)
{
    uint32_t tab[4];
    tab[0] = v0 >> 32;
    tab[1] = v0;
    tab[2] = v1 >> 32;
    tab[3] = v1;
    fdt_prop_tab_u32(s, prop_name, tab, 4);
}

static void fdt_prop_str(FDTState *s, const char *prop_name,
                         const char *str)
{
    fdt_prop(s, prop_name, str, strlen(str) + 1);
}

/* NULL terminated string list */
static void fdt_prop_tab_str(FDTState *s, const char *prop_name, ...)
{
    va_list ap;

    va_start(ap, prop_name);
    int size = 0;
    for (;;) {
        char *ptr = va_arg(ap, char *);
        if (!ptr)
            break;
        int str_size = strlen(ptr) + 1;
        size += str_size;
    }
    va_end(ap);

    char *tab = (char *)malloc(size);
    va_start(ap, prop_name);
    size = 0;
    for (;;) {
        char *ptr = va_arg(ap, char *);
        if (!ptr)
            break;
        int str_size = strlen(ptr) + 1;
        memcpy(tab + size, ptr, str_size);
        size += str_size;
    }
    va_end(ap);

    fdt_prop(s, prop_name, tab, size);
    free(tab);
}

/* write the FDT to 'dst1'. return the FDT size in bytes */
int fdt_output(FDTState *s, uint8_t *dst)
{
    struct fdt_header *h;
    struct fdt_reserve_entry *re;
    int dt_struct_size;
    int dt_strings_size;
    int pos;

    assert(s->open_node_count == 0);

    fdt_put32(s, FDT_END);

    dt_struct_size = s->tab_len * sizeof(uint32_t);
    dt_strings_size = s->string_table_len;

    h = (struct fdt_header *)dst;
    h->magic = cpu_to_be32(FDT_MAGIC);
    h->version = cpu_to_be32(FDT_VERSION);
    h->last_comp_version = cpu_to_be32(16);
    h->boot_cpuid_phys = cpu_to_be32(0);
    h->size_dt_strings = cpu_to_be32(dt_strings_size);
    h->size_dt_struct = cpu_to_be32(dt_struct_size);

    pos = sizeof(struct fdt_header);

    h->off_dt_struct = cpu_to_be32(pos);
    memcpy(dst + pos, s->tab, dt_struct_size);
    pos += dt_struct_size;

    /* align to 8 */
    while ((pos & 7) != 0) {
        dst[pos++] = 0;
    }
    h->off_mem_rsvmap = cpu_to_be32(pos);
    re = (struct fdt_reserve_entry *)(dst + pos);
    re->address = 0; /* no reserved entry */
    re->size = 0;
    pos += sizeof(struct fdt_reserve_entry);

    h->off_dt_strings = cpu_to_be32(pos);
    memcpy(dst + pos, s->string_table, dt_strings_size);
    pos += dt_strings_size;

    /* align to 8, just in case */
    while ((pos & 7) != 0) {
        dst[pos++] = 0;
    }

    h->totalsize = cpu_to_be32(pos);
    return pos;
}

void fdt_end(FDTState *s)
{
    free(s->tab);
    free(s->string_table);
    free(s);
}

static int riscv_build_fdt(RISCVMachine *m, uint8_t *dst, const char *dtb_name,
                           const char *cmd_line, uint64_t initrd_start, uint64_t initrd_end)
{
    FDTState *s = 0;
    int size;
    if (!dtb_name) {
        int intc_phandle = 0;
        int max_xlen, i, cur_phandle, plic_phandle;
        char isa_string[128], *q;
        uint32_t misa;
        uint32_t tab[4*MAX_CPUS];
        FBDevice *fb_dev;

        s = fdt_init();

        cur_phandle = 1;

        fdt_begin_node(s, "");
        fdt_prop_u32(s, "#address-cells", 2);
        fdt_prop_u32(s, "#size-cells", 2);
        fdt_prop_str(s, "compatible", "ucbbar,dromajo-bar_dev");
        fdt_prop_str(s, "model", "ucbbar,dromajo-bare");

        /* CPU list */
        fdt_begin_node(s, "cpus");
        fdt_prop_u32(s, "#address-cells", 1);
        fdt_prop_u32(s, "#size-cells", 0);
        fdt_prop_u32(s, "timebase-frequency", RTC_FREQ);

        int hartid2handle[MAX_CPUS];

        for (int hartid = 0; hartid < m->ncpus; ++hartid) {
            /* cpu */
            fdt_begin_node_num(s, "cpu", hartid);
            fdt_prop_str(s, "device_type", "cpu");
            fdt_prop_u32(s, "reg", hartid);
            fdt_prop_str(s, "status", "okay");
            fdt_prop_str(s, "compatible", "riscv");

            max_xlen = 64;
            misa = riscv_cpu_get_misa(m->cpu_state[hartid]);
            q = isa_string;
            q += snprintf(isa_string, sizeof(isa_string), "rv%d", max_xlen);
            for (i = 0; i < 26; ++i) {
                if (misa & (1 << i))
                    *q++ = 'a' + i;
            }
            *q = '\0';
            fdt_prop_str(s, "riscv,isa", isa_string);

            fdt_prop_str(s, "mmu-type", max_xlen <= 32 ? "riscv,sv32" : "riscv,sv48");
            fdt_prop_u32(s, "clock-frequency", 2000000000);

            fdt_begin_node(s, "interrupt-controller");
            fdt_prop_u32(s, "#interrupt-cells", 1);
            fdt_prop(s, "interrupt-controller", NULL, 0);
            fdt_prop_str(s, "compatible", "riscv,cpu-intc");
            intc_phandle = cur_phandle++;
            hartid2handle[hartid] = intc_phandle;
            fdt_prop_u32(s, "phandle", intc_phandle);
            fdt_prop_u32(s, "linux,phandle", intc_phandle);
            fdt_end_node(s); /* interrupt-controller */

            fdt_end_node(s); /* cpu */
        }

        fdt_end_node(s); /* cpus */

        fdt_begin_node_num(s, "memory", m->ram_base_addr);
        fdt_prop_str(s, "device_type", "memory");
        tab[0] = m->ram_base_addr >> 32;
        tab[1] = m->ram_base_addr;
        tab[2] = m->ram_size >> 32;
        tab[3] = m->ram_size;
        fdt_prop_tab_u32(s, "reg", tab, 4);

        fdt_end_node(s); /* memory */

        fdt_begin_node(s, "soc");
        fdt_prop_u32(s, "#address-cells", 2);
        fdt_prop_u32(s, "#size-cells", 2);
        fdt_prop_tab_str(s, "compatible",
                        "ucbbar,dromajo-bar-soc", "simple-bus", NULL);
        fdt_prop(s, "ranges", NULL, 0);

        fdt_begin_node_num(s, "clint", m->clint_base_addr);
        fdt_prop_str(s, "compatible", "riscv,clint0");

        for (int hartid = 0; hartid < m->ncpus; ++hartid) {
            tab[hartid * 4 + 0] = hartid2handle[hartid];
            tab[hartid * 4 + 1] = 3; /* M IPI irq */
            tab[hartid * 4 + 2] = hartid2handle[hartid];
            tab[hartid * 4 + 3] = 7; /* M timer irq */
        }

        fdt_prop_tab_u32(s, "interrupts-extended", tab, 4 * m->ncpus);

        fdt_prop_tab_u64_2(s, "reg", m->clint_base_addr, m->clint_size);

        fdt_end_node(s); /* clint */

        fdt_begin_node_num(s, "plic", m->plic_base_addr);
        fdt_prop_u32(s, "#interrupt-cells", 1);

        fdt_prop(s, "interrupt-controller", NULL, 0);
        fdt_prop_str(s, "compatible", "riscv,plic0");
        fdt_prop_u32(s, "riscv,ndev", 31);
        fdt_prop_tab_u64_2(s, "reg", m->plic_base_addr, m->plic_size);

        for (int hartid = 0; hartid < m->ncpus; ++hartid) {
            tab[hartid * 4 + 0] = hartid2handle[hartid];
            tab[hartid * 4 + 1] = 9; /* S ext irq */
            tab[hartid * 4 + 2] = hartid2handle[hartid];
            tab[hartid * 4 + 3] = 11; /* M ext irq */
        }

        fdt_prop_tab_u32(s, "interrupts-extended", tab, m->ncpus * 4);

        plic_phandle = cur_phandle++;
        fdt_prop_u32(s, "phandle", plic_phandle);

        fdt_end_node(s); /* plic */

        for (i = 0; i < m->virtio_count; ++i) {
            fdt_begin_node_num(s, "virtio", VIRTIO_BASE_ADDR + i * VIRTIO_SIZE);
            fdt_prop_str(s, "compatible", "virtio,mmio");
            fdt_prop_tab_u64_2(s, "reg", VIRTIO_BASE_ADDR + i * VIRTIO_SIZE, VIRTIO_SIZE);
            tab[0] = plic_phandle;
            tab[1] = VIRTIO_IRQ + i;
            fdt_prop_tab_u32(s, "interrupts-extended", tab, 2);
            fdt_end_node(s); /* virtio */
        }

#ifdef USE_SIFIVE_UART
        // SiFive UART
        fdt_begin_node_num(s, "uart", UART0_BASE_ADDR);
        fdt_prop_str(s, "compatible", "sifive,uart0");
        fdt_prop_tab_u64_2(s, "reg", UART0_BASE_ADDR, UART0_SIZE);
        fdt_end_node(s); /* uart */
#endif

        // Fake Synopsys™ DesignWare™ ABP™ UART (NS16550 compatible)
        fdt_begin_node_num(s, "uart", DW_APB_UART0_BASE_ADDR); {
            fdt_prop_str(s, "compatible", "ns16550");
            fdt_prop_tab_u64_2(s, "reg", DW_APB_UART0_BASE_ADDR, DW_APB_UART0_SIZE);
            fdt_prop_u32(s, "reg-shift", 2);
            fdt_prop_u32(s, "reg-io-width", 4);
            // No interrupts?
        } fdt_end_node(s);

        fb_dev = m->common.fb_dev;
        if (fb_dev) {
            fdt_begin_node_num(s, "framebuffer", FRAMEBUFFER_BASE_ADDR);
            fdt_prop_str(s, "compatible", "simple-framebuffer");
            fdt_prop_tab_u64_2(s, "reg", FRAMEBUFFER_BASE_ADDR, fb_dev->fb_size);
            fdt_prop_u32(s, "width", fb_dev->width);
            fdt_prop_u32(s, "height", fb_dev->height);
            fdt_prop_u32(s, "stride", fb_dev->stride);
            fdt_prop_str(s, "format", "a8r8g8b8");
            fdt_end_node(s); /* framebuffer */
        }

        fdt_end_node(s); /* soc */

        fdt_begin_node(s, "chosen");
        fdt_prop_str(s, "bootargs", cmd_line ? cmd_line : "");
        if (initrd_start && initrd_start < initrd_end) {
            fdt_prop_u64(s, "linux,initrd-start", initrd_start);
            fdt_prop_u64(s, "linux,initrd-end", initrd_end);
        }

        fdt_end_node(s); /* chosen */

        fdt_end_node(s); /* / */

        size = fdt_output(s, dst);
    } else {
        // write from other dts
        FILE *fPtr;
        unsigned long fLen;

        fPtr = fopen(dtb_name, "rb");  // Open the file in binary mode
        fseek(fPtr, 0, SEEK_END);  // Jump to the end of the file
        fLen = ftell(fPtr);     // Get the current byte offset in the file
        rewind(fPtr);              // Jump back to the beginning of the file

        size_t result = fread((char*)dst, sizeof(uint8_t), fLen, fPtr); // Read in the entire file
        if (result != fLen) {
            fprintf(dromajo_stderr,
                    "DROMAJO failed reading the dts string\n");
            return -1;
        }

        // DEBUG
        //for (unsigned long i = 0; i < fLen; ++i)
        //    printf("[DEBUG][%p][%ld/%ld] == 0x%x\n", &dst[i], i, fLen, dst[i]);
        //printf("[DEBUG] Done printing\n");

        fclose(fPtr); // Close the file

        size = fLen;
    }

#ifdef DUMP_DTB
    {
        FILE *f = fopen("dromajo.dtb", "wb");
        if (f == nullptr) {
            fprintf(dromajo_stderr, "DROMAJO failed to open dromajo.dtb dump file (disable DUMP_DTB?)\n");
            return -1;
        }
        fwrite(dst, 1, size, f);
        fclose(f);
    }
#endif

    if (!dtb_name)
        fdt_end(s);

    return size;
}

static void load_elf_image(RISCVMachine *s, const uint8_t *image, size_t image_len)
{
    Elf64_Ehdr *ehdr = (Elf64_Ehdr *)image;
    const Elf64_Phdr *ph = (Elf64_Phdr *)(image + ehdr->e_phoff);

    for (int i = 0; i < ehdr->e_phnum; ++i, ++ph)
        if (ph->p_type == PT_LOAD) {
            size_t rounded_size = ph->p_memsz;
            rounded_size = (rounded_size + DEVRAM_PAGE_SIZE - 1) & ~(DEVRAM_PAGE_SIZE - 1);
            PhysMemoryRange *pr = get_phys_mem_range(s->mem_map, ph->p_vaddr);
            if (pr->addr != RAM_BASE_ADDR)
                cpu_register_ram(s->mem_map, ph->p_vaddr, rounded_size, 0);
            memcpy(get_ram_ptr(s, ph->p_vaddr), image + ph->p_offset, ph->p_filesz);
        }
}

static int load_bootrom(const char *bootrom_name, uint32_t *location)
{
    FILE *fPtr;
    unsigned long fLen;

    fPtr = fopen(bootrom_name, "rb");  // Open the file in binary mode
    fseek(fPtr, 0, SEEK_END);  // Jump to the end of the file
    fLen = ftell(fPtr);     // Get the current byte offset in the file
    rewind(fPtr);              // Jump back to the beginning of the file

    size_t result = fread((char*)location, sizeof(uint8_t), fLen, fPtr); // Read in the entire file
    if (result != fLen) {
        fprintf(dromajo_stderr,
                "DROMAJO failed reading the bootrom image\n");
        return -1;
    }

    // DEBUG
    //for (unsigned long i = 0; i < (fLen/sizeof(uint32_t)); ++i)
    //    printf("[DEBUG][%p][%ld/%ld] == 0x%x\n", &location[i], i, fLen/sizeof(uint32_t), location[i]);

    fclose(fPtr); // Close the file

    return fLen;
}

/* Return non-zero on failure */
static int copy_kernel(RISCVMachine *s,
                       const uint8_t *fw_buf, size_t fw_buf_len,
                       const uint8_t *kernel_buf, size_t kernel_buf_len,
                       const uint8_t *initrd_buf, size_t initrd_buf_len,
                       const char *bootrom_name, const char *dtb_name,
                       const char *cmd_line)
{
    uint64_t initrd_start = 0, initrd_end = 0;

    if (fw_buf_len > s->ram_size) {
        vm_error("Firmware too big\n");
        return 1;
    }

    // load firmware into ram
    if (elf64_is_riscv64(fw_buf, fw_buf_len)) {
        // XXX if the ELF is given in the config file, then we don't get to set memory base based on that.

        if (elf64_get_entrypoint(fw_buf) != s->ram_base_addr) {
            fprintf(dromajo_stderr,
                    "DROMAJO currently requires a 0x%" PRIx64 " starting address, image assumes 0x%0" PRIx64 "\n",
                    s->ram_base_addr,
                    elf64_get_entrypoint(fw_buf));
            return 1;
        }

        load_elf_image(s, fw_buf, fw_buf_len);
        elf64_find_global(fw_buf, fw_buf_len, "tohost", &s->htif_tohost_addr);
    }
    else
        memcpy(get_ram_ptr(s, s->ram_base_addr), fw_buf, fw_buf_len);

    if (!(s->ram_base_addr == 0x80000000 || s->ram_base_addr == 0x8000000000 || s->ram_base_addr == 0xC000000000)) {
        fprintf(dromajo_stderr,
                "DROMAJO currently requires a 0x80000000 or 0x8000000000 or 0xC000000000"
                " ram starting address, image assumes 0x%0" PRIx64 "\n",
                elf64_get_entrypoint(fw_buf));
        assert(0);
    }

    // load kernel into ram
    if (kernel_buf && kernel_buf_len) {
        if (s->ram_size <= KERNEL_OFFSET) {
            vm_error("Can't load kernel at ram offset 0x%x\n", KERNEL_OFFSET);
            return 1;
        }
        if (kernel_buf_len > (s->ram_size - KERNEL_OFFSET)) {
            vm_error("Kernel too big\n");
            return 1;
        }
        memcpy(get_ram_ptr(s, s->ram_base_addr + KERNEL_OFFSET), kernel_buf, kernel_buf_len);
    }

    // load initrd into ram
    if (initrd_buf && initrd_buf_len) {
        if (initrd_buf_len > s->ram_size) {
            vm_error("Initrd too big\n");
            return 1;
        }
        initrd_end = s->ram_base_addr + s->ram_size;
        initrd_start = initrd_end - initrd_buf_len;
        initrd_start = (initrd_start >> 12) << 12;
        memcpy(get_ram_ptr(s, initrd_start), initrd_buf, initrd_buf_len);
    }

    // setup the bootrom
    uint8_t *ram_ptr = get_ram_ptr(s, ROM_BASE_ADDR);
    uint32_t *q      = (uint32_t *)(ram_ptr + (BOOT_BASE_ADDR - ROM_BASE_ADDR));
    uint32_t bootromSzBytes = 0;

    /* KEEP THIS IN SYNC WITH THE TARGET BOOTROM */
    if (bootrom_name) {
        // read in the bootrom from the file
        bootromSzBytes = load_bootrom(bootrom_name, q);
        if (bootromSzBytes < 0)
            return 1;
    } else {
        // use the hardcoded bootrom
        *q++ = 0xf1402573;  // start:  csrr   a0, mhartid
        if (s->ncpus == 1) {
            *q++ = 0x00050663;  //         beqz   a0, 1f
            *q++ = 0x10500073;  // 0:      wfi
            *q++ = 0xffdff06f;  //         j      0b
        } else {
            *q++ = 0x00000013; // nop
            *q++ = 0x00000013; // nop
            *q++ = 0x00000013; // nop
        }
        *q++ = 0x00000597;  // 1:      auipc  a1, 0x0
        *q++ = 0x0f058593;  //         addi   a1, a1, 240 # _start + 256
        *q++ = 0x60300413;  //         li     s0, 1539
        *q++ = 0x7b041073;  //         csrw   dcsr, s0
        if (s->ram_base_addr == 0xC000000000) {
            *q++ = 0x0030041b;  //         addiw  s0, zero, 3
            *q++ = 0x02641413;  //         slli   s0, s0, 38
        } else {
            *q++ = 0x0010041b;  //         addiw  s0, zero, 1
            if (s->ram_base_addr == 0x80000000)
                *q++ = 0x01f41413; //     slli s0, s0, 31
            else
                *q++ = 0x02741413;  //         slli   s0, s0, 39
        }
        *q++ = 0x7b141073;  //         csrw   dpc, s0
        *q++ = 0x7b200073;  //         dret
        bootromSzBytes = 13*sizeof(uint32_t);
    }

    // setup the dtb
    uint32_t fdt_off = (BOOT_BASE_ADDR - ROM_BASE_ADDR);
    if (s->compact_bootrom)
        fdt_off += bootromSzBytes;
    else
        fdt_off += 256;

    if(riscv_build_fdt(s, ram_ptr + fdt_off, dtb_name,
                       cmd_line, initrd_start, initrd_end) < 0)
        return -1;

    for (int i = 0; i < s->ncpus; ++i)
        riscv_set_debug_mode(s->cpu_state[i], TRUE);

    return 0;
}

static void riscv_flush_tlb_write_range(void *opaque, uint8_t *ram_addr,
                                        size_t ram_size)
{
    RISCVMachine *s = (RISCVMachine *)opaque;
    for (int i = 0; i < s->ncpus; ++i)
        riscv_cpu_flush_tlb_write_range_ram(s->cpu_state[i], ram_addr, ram_size);
}

void virt_machine_set_defaults(VirtMachineParams *p)
{
    memset(p, 0, sizeof *p);
    p->physical_addr_len = PHYSICAL_ADDR_LEN_DEFAULT;
    p->ram_base_addr     = RAM_BASE_ADDR;
    p->reset_vector      = BOOT_BASE_ADDR;
    p->plic_base_addr    = PLIC_BASE_ADDR;
    p->plic_size         = PLIC_SIZE;
    p->clint_base_addr   = CLINT_BASE_ADDR;
    p->clint_size        = CLINT_SIZE;
}

RISCVMachine *virt_machine_init(const VirtMachineParams *p)
{
    VIRTIODevice *blk_dev;
    int irq_num, i;
    VIRTIOBusDef vbus_s, *vbus = &vbus_s;
    RISCVMachine *s = (RISCVMachine *)mallocz(sizeof *s);

    s->ram_size = p->ram_size;
    s->ram_base_addr = p->ram_base_addr;

    s->mem_map = phys_mem_map_init();
    /* needed to handle the RAM dirty bits */
    s->mem_map->opaque = s;
    s->mem_map->flush_tlb_write_range = riscv_flush_tlb_write_range;
    s->common.maxinsns = p->maxinsns;
    s->common.snapshot_load_name = p->snapshot_load_name;

    s->ncpus = p->ncpus;

    /* setup reset vector for core
     * note: must be above riscv_cpu_init
     */
    s->reset_vector = p->reset_vector;

    /* get missings csrs, not all cores support all csrs */
    s->missing_csrs      = p->missing_csrs;
    s->missing_csrs_size = p->missing_csrs_size;

    /* some implementations hide commits of some instructions (ex: ecall, ebreak)*/
    s->skip_commit       = p->skip_commit;
    s->skip_commit_size  = p->skip_commit_size;

    /* have compact bootrom */
    s->compact_bootrom = p->compact_bootrom;

    /* add custom extension bit to misa */
    s->custom_extension = p->custom_extension;

    s->plic_base_addr  = p->plic_base_addr;
    s->plic_size       = p->plic_size;
    s->clint_base_addr = p->clint_base_addr;
    s->clint_size      = p->clint_size;

    if (MAX_CPUS < s->ncpus) {
        fprintf(stderr, "ERROR: ncpus:%d exceeds maximum MAX_CPU\n", s->ncpus);
        exit(3);
    }

    for (int i = 0; i < s->ncpus; ++i) {
        s->cpu_state[i] = riscv_cpu_init(s, i);
    }

    /* RAM */
    //cpu_register_ram(s->mem_map, 0, 4096, 0); // Have memory at 0 for uaccess-etcsr to pass
    cpu_register_ram(s->mem_map, s->ram_base_addr, s->ram_size, 0);
    cpu_register_ram(s->mem_map, ROM_BASE_ADDR, ROM_SIZE, 0);

    for (int i = 0; i < s->ncpus; ++i) {
        s->cpu_state[i]->physical_addr_len = p->physical_addr_len;
    }

    if (p->mmio_start) {
        uint64_t sz = p->mmio_end - p->mmio_start;
        cpu_register_device(s->mem_map, p->mmio_start, sz, 0,
                            mmio_read, mmio_write, DEVIO_SIZE32 | DEVIO_SIZE16 | DEVIO_SIZE8);
    }

    if (p->mmio_addrset_size > 0) {
        for (size_t i = 0; i < p->mmio_addrset_size; ++i) {
            uint64_t sz = p->mmio_addrset[i].size;
            cpu_register_device(s->mem_map, p->mmio_addrset[i].start, sz, 0,
                                mmio_read, mmio_write, DEVIO_SIZE32 | DEVIO_SIZE16 | DEVIO_SIZE8);
        }
    }

    SiFiveUARTState *uart = (SiFiveUARTState *)calloc(sizeof *uart, 1);
    uart->irq = UART0_IRQ;
    uart->cs  = p->console;
    cpu_register_device(s->mem_map, UART0_BASE_ADDR, UART0_SIZE, uart,
                        uart_read, uart_write, DEVIO_SIZE32);

    DW_apb_uart_state *dw_apb_uart = (DW_apb_uart_state *)calloc(sizeof *dw_apb_uart, 1);
    dw_apb_uart->irq = DW_APB_UART0_IRQ;
    dw_apb_uart->cs  = p->console;
    cpu_register_device(s->mem_map, DW_APB_UART0_BASE_ADDR, DW_APB_UART0_SIZE,
                        dw_apb_uart, dw_apb_uart_read, dw_apb_uart_write,
                        DEVIO_SIZE32 | DEVIO_SIZE16 | DEVIO_SIZE8);

    cpu_register_device(s->mem_map, p->clint_base_addr, p->clint_size, s,
                        clint_read, clint_write, DEVIO_SIZE32 | DEVIO_SIZE16 | DEVIO_SIZE8);
    cpu_register_device(s->mem_map, p->plic_base_addr, p->plic_size, s,
                        plic_read, plic_write, DEVIO_SIZE32);

    for (int j = 1; j < 32; j++) {
        irq_init(&s->plic_irq[j], plic_set_irq, s, j);
    }

    s->htif_tohost_addr = p->htif_base_addr;

    s->common.console = p->console;

    memset(vbus, 0, sizeof(*vbus));
    vbus->mem_map = s->mem_map;
    vbus->addr = VIRTIO_BASE_ADDR;
    irq_num = VIRTIO_IRQ;

    /* virtio console */
    if (p->console) {
        vbus->irq = &s->plic_irq[irq_num];
        s->common.console_dev = virtio_console_init(vbus, p->console);
        vbus->addr += VIRTIO_SIZE;
        irq_num++;
        s->virtio_count++;
    }

    /* virtio net device */
    for (i = 0; i < p->eth_count; ++i) {
        vbus->irq = &s->plic_irq[irq_num];
        virtio_net_init(vbus, p->tab_eth[i].net);
        s->common.net = p->tab_eth[i].net;
        vbus->addr += VIRTIO_SIZE;
        irq_num++;
        s->virtio_count++;
    }

    /* virtio block device */
    for (i = 0; i < p->drive_count; ++i) {
        vbus->irq = &s->plic_irq[irq_num];
        blk_dev = virtio_block_init(vbus, p->tab_drive[i].block_dev);
        (void)blk_dev;
        vbus->addr += VIRTIO_SIZE;
        irq_num++;
        s->virtio_count++;
    }

    /* virtio filesystem */
    for (i = 0; i < p->fs_count; ++i) {
        VIRTIODevice *fs_dev;
        vbus->irq = &s->plic_irq[irq_num];
        fs_dev = virtio_9p_init(vbus, p->tab_fs[i].fs_dev, p->tab_fs[i].tag);
        (void)fs_dev;
        vbus->addr += VIRTIO_SIZE;
        irq_num++;
        s->virtio_count++;
    }

    if (p->input_device) {
        if (!strcmp(p->input_device, "virtio")) {
            vbus->irq = &s->plic_irq[irq_num];
            s->keyboard_dev = virtio_input_init(vbus, VIRTIO_INPUT_TYPE_KEYBOARD);
            vbus->addr += VIRTIO_SIZE;
            irq_num++;
            s->virtio_count++;

            vbus->irq = &s->plic_irq[irq_num];
            s->mouse_dev = virtio_input_init(vbus, VIRTIO_INPUT_TYPE_TABLET);
            vbus->addr += VIRTIO_SIZE;
            irq_num++;
            s->virtio_count++;
        } else {
            vm_error("unsupported input device: %s\n", p->input_device);
            exit(1);
        }
    }

    if (!p->files[VM_FILE_BIOS].buf) {
        vm_error("No bios given\n");
        return NULL;
    } else if (copy_kernel(s,
                           p->files[VM_FILE_BIOS].buf,
                           p->files[VM_FILE_BIOS].len,
                           p->files[VM_FILE_KERNEL].buf,
                           p->files[VM_FILE_KERNEL].len,
                           p->files[VM_FILE_INITRD].buf,
                           p->files[VM_FILE_INITRD].len,
                           p->bootrom_name,
                           p->dtb_name,
                           p->cmdline))
        return NULL;

    /* mmio setup for cosim */
    s->mmio_start = p->mmio_start;
    s->mmio_end   = p->mmio_end;
    s->mmio_addrset = p->mmio_addrset;
    s->mmio_addrset_size = p->mmio_addrset_size;

    /* interrupts and exception setup for cosim */
    s->common.cosim = false;
    s->common.pending_exception = -1;
    s->common.pending_interrupt = -1;

    /* plic/clint setup */
    s->plic_base_addr  = p->plic_base_addr;
    s->plic_size       = p->plic_size;
    s->clint_base_addr = p->clint_base_addr;
    s->clint_size      = p->clint_size;

    if (p->dump_memories) {
      FILE *fd = fopen("BootRAM.hex", "w+");
      if (fd==0) {
        fprintf(stderr, "ERROR: could not create BootRAM.hex\n");
        exit(-3);
      }

      uint8_t *ram_ptr  = get_ram_ptr(s, ROM_BASE_ADDR);
      for(int i=0;i<ROM_SIZE/4;++i) {
        uint32_t *q_base = (uint32_t *)(ram_ptr + (BOOT_BASE_ADDR - ROM_BASE_ADDR));
        fprintf(fd,"@%06x %08x\n",i, q_base[i]);
      }
      fclose(fd);
    }

    return s;
}

void virt_machine_end(RISCVMachine *s)
{
    if (s->common.snapshot_save_name)
        virt_machine_serialize(s, s->common.snapshot_save_name);

    /* XXX: stop all */
    for (int i = 0; i < s->ncpus; ++i) {
        riscv_cpu_end(s->cpu_state[i]);
    }

    if (s->mmio_addrset_size > 0)
        free(s->mmio_addrset);

    phys_mem_map_end(s->mem_map);
    free(s);
}

void virt_machine_serialize(RISCVMachine *m, const char *dump_name)
{
    RISCVCPUState *s = m->cpu_state[0]; // FIXME: MULTICORE

    fprintf(dromajo_stderr, "plic: %x %x timecmp=%llx\n",
            m->plic_pending_irq, m->plic_served_irq, (unsigned long long)s->timecmp);

    assert(m->ncpus == 1); // FIXME: riscv_cpu_serialize must be patched for multicore
    riscv_cpu_serialize(s, dump_name, m->clint_base_addr);
}

void virt_machine_deserialize(RISCVMachine *m, const char *dump_name)
{
    RISCVCPUState *s = m->cpu_state[0]; // FIXME: MULTICORE

    assert(m->ncpus == 1); // FIXME: riscv_cpu_serialize must be patched for multicore
    riscv_cpu_deserialize(s, dump_name);
}

int virt_machine_get_sleep_duration(RISCVMachine *m, int hartid, int ms_delay)
{
    RISCVCPUState *s = m->cpu_state[hartid];
    int64_t ms_delay1;

    /* wait for an event: the only asynchronous event is the RTC timer */
    if (!(riscv_cpu_get_mip(s) & MIP_MTIP) && rtc_get_time(m) > 0) {
        ms_delay1 = s->timecmp - rtc_get_time(m);
        if (ms_delay1 <= 0) {
            riscv_cpu_set_mip(s, MIP_MTIP);
            ms_delay = 0;
        } else {
            /* convert delay to ms */
            ms_delay1 = ms_delay1 / (RTC_FREQ / 1000);
            if (ms_delay1 < ms_delay)
                ms_delay = ms_delay1;
        }
    }

    if (!riscv_cpu_get_power_down(s))
        ms_delay = 0;

    return ms_delay;
}

uint64_t virt_machine_get_pc(RISCVMachine *s, int hartid)
{
    return riscv_get_pc(s->cpu_state[hartid]);
}

uint64_t virt_machine_get_reg(RISCVMachine *s, int hartid, int rn)
{
    return riscv_get_reg(s->cpu_state[hartid], rn);
}

uint64_t virt_machine_get_fpreg(RISCVMachine *s, int hartid, int rn)
{
    return riscv_get_fpreg(s->cpu_state[hartid], rn);
}

const char *virt_machine_get_name(void)
{
    return "riscv64";
}

void vm_send_key_event(RISCVMachine *s, BOOL is_down, uint16_t key_code)
{
    if (s->keyboard_dev) {
        virtio_input_send_key_event(s->keyboard_dev, is_down, key_code);
    }
}

BOOL vm_mouse_is_absolute(RISCVMachine *s)
{
    return TRUE;
}

void vm_send_mouse_event(RISCVMachine *s, int dx, int dy, int dz, unsigned buttons)
{
    if (s->mouse_dev) {
        virtio_input_send_mouse_event(s->mouse_dev, dx, dy, dz, buttons);
    }
}
