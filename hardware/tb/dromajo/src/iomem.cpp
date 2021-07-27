/*
 * IO memory handling
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
#include <string.h>
#include <inttypes.h>
#include <assert.h>

#include "cutils.h"
#include "iomem.h"

static PhysMemoryRange *default_register_ram(PhysMemoryMap *s, uint64_t addr,
                                             uint64_t size, int devram_flags);
static void default_free_ram(PhysMemoryMap *s, PhysMemoryRange *pr);
static const uint32_t *default_get_dirty_bits(PhysMemoryMap *map, PhysMemoryRange *pr);
static void default_set_addr(PhysMemoryMap *map,
                             PhysMemoryRange *pr, uint64_t addr, BOOL enabled);

PhysMemoryMap *phys_mem_map_init(void)
{
    PhysMemoryMap *s = (PhysMemoryMap *)mallocz(sizeof(PhysMemoryMap));
    s->register_ram = default_register_ram;
    s->free_ram = default_free_ram;
    s->get_dirty_bits = default_get_dirty_bits;
    s->set_ram_addr = default_set_addr;
    return s;
}

void phys_mem_map_end(PhysMemoryMap *s)
{
    for (int i = 0; i < s->n_phys_mem_range; i++) {
        PhysMemoryRange *pr = &s->phys_mem_range[i];
        if (pr->is_ram) {
            s->free_ram(s, pr);
        }
    }

    free(s);
}

/* return NULL if not found */
/* XXX: optimize */
PhysMemoryRange *get_phys_mem_range(PhysMemoryMap *s, uint64_t paddr)
{
    for (int i = s->n_phys_mem_range-1; i >= 0; --i) {
        PhysMemoryRange *pr = &s->phys_mem_range[i];
        if (paddr >= pr->addr && paddr < pr->addr + pr->size)
            return pr;
    }

    return NULL;
}

PhysMemoryRange *register_ram_entry(PhysMemoryMap *s, uint64_t addr,
                                    uint64_t size, int devram_flags)
{
    PhysMemoryRange *pr;

    assert(s->n_phys_mem_range < PHYS_MEM_RANGE_MAX);
    assert((size & (DEVRAM_PAGE_SIZE - 1)) == 0 && size != 0);
    pr = &s->phys_mem_range[s->n_phys_mem_range++];
    pr->map = s;
    pr->is_ram = TRUE;
    pr->devram_flags = devram_flags & ~DEVRAM_FLAG_DISABLED;
    pr->addr = addr;
    pr->org_size = size;
    if (devram_flags & DEVRAM_FLAG_DISABLED)
        pr->size = 0;
    else
        pr->size = pr->org_size;
    pr->phys_mem = NULL;
    pr->dirty_bits = NULL;
    return pr;
}

static PhysMemoryRange *default_register_ram(PhysMemoryMap *s, uint64_t addr,
                                             uint64_t size, int devram_flags)
{
    PhysMemoryRange *pr;

    pr = register_ram_entry(s, addr, size, devram_flags);

    pr->phys_mem = (uint8_t *)mallocz(size);
    if (!pr->phys_mem) {
        fprintf(dromajo_stderr, "Could not allocate VM memory\n");
        exit(1);
    }

    if (devram_flags & DEVRAM_FLAG_DIRTY_BITS) {
        size_t nb_pages;
        int i;
        nb_pages = size >> DEVRAM_PAGE_SIZE_LOG2;
        pr->dirty_bits_size = ((nb_pages + 31) / 32) * sizeof(uint32_t);
        pr->dirty_bits_index = 0;
        for (i = 0; i < 2; i++) {
            pr->dirty_bits_tab[i] = (uint32_t *)mallocz(pr->dirty_bits_size);
        }
        pr->dirty_bits = pr->dirty_bits_tab[pr->dirty_bits_index];
    }
    return pr;
}

/* return a pointer to the bitmap of dirty bits and reset them */
static const uint32_t *default_get_dirty_bits(PhysMemoryMap *map,
                                              PhysMemoryRange *pr)
{
    uint32_t *dirty_bits;
    BOOL has_dirty_bits;
    size_t n, i;

    dirty_bits = pr->dirty_bits;

    has_dirty_bits = FALSE;
    n = pr->dirty_bits_size / sizeof(uint32_t);
    for (i = 0; i < n; i++) {
        if (dirty_bits[i] != 0) {
            has_dirty_bits = TRUE;
            break;
        }
    }
    if (has_dirty_bits && pr->size != 0) {
        /* invalidate the corresponding CPU write TLBs */
        map->flush_tlb_write_range(map->opaque, pr->phys_mem, pr->org_size);
    }

    pr->dirty_bits_index ^= 1;
    pr->dirty_bits = pr->dirty_bits_tab[pr->dirty_bits_index];
    memset(pr->dirty_bits, 0, pr->dirty_bits_size);
    return dirty_bits;
}

static void default_free_ram(PhysMemoryMap *s, PhysMemoryRange *pr)
{
    free(pr->phys_mem);
}

PhysMemoryRange *cpu_register_device(PhysMemoryMap *s, uint64_t addr,
                                     uint64_t size, void *opaque,
                                     DeviceReadFunc *read_func, DeviceWriteFunc *write_func,
                                     int devio_flags)
{
    PhysMemoryRange *pr;
    assert(s->n_phys_mem_range < PHYS_MEM_RANGE_MAX);
    assert(size <= 0xffffffff);
    pr = &s->phys_mem_range[s->n_phys_mem_range++];
    pr->map = s;
    pr->addr = addr;
    pr->org_size = size;
    if (devio_flags & DEVIO_DISABLED)
        pr->size = 0;
    else
        pr->size = pr->org_size;
    pr->is_ram = FALSE;
    pr->opaque = opaque;
    pr->read_func = read_func;
    pr->write_func = write_func;
    pr->devio_flags = devio_flags;
    return pr;
}

static void default_set_addr(PhysMemoryMap *map,
                             PhysMemoryRange *pr, uint64_t addr, BOOL enabled)
{
    if (enabled) {
        if (pr->size == 0 || pr->addr != addr) {
            /* enable or move mapping */
            if (pr->is_ram) {
                map->flush_tlb_write_range(map->opaque,
                                           pr->phys_mem, pr->org_size);
            }
            pr->addr = addr;
            pr->size = pr->org_size;
        }
    } else {
        if (pr->size != 0) {
            /* disable mapping */
            if (pr->is_ram) {
                map->flush_tlb_write_range(map->opaque,
                                           pr->phys_mem, pr->org_size);
            }
            pr->addr = 0;
            pr->size = 0;
        }
    }
}

void phys_mem_set_addr(PhysMemoryRange *pr, uint64_t addr, BOOL enabled)
{
    PhysMemoryMap *map = pr->map;
    if (!pr->is_ram) {
        default_set_addr(map, pr, addr, enabled);
    } else {
        return map->set_ram_addr(map, pr, addr, enabled);
    }
}

/* IRQ support */

void irq_init(IRQSignal *irq, SetIRQFunc *set_irq, void *opaque, int irq_num)
{
    irq->set_irq = set_irq;
    irq->opaque = opaque;
    irq->irq_num = irq_num;
}
