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
#ifndef IOMEM_H
#define IOMEM_H

#include "cutils.h"

typedef void DeviceWriteFunc(void *opaque, uint32_t offset,
                             uint32_t val, int size_log2);
typedef uint32_t DeviceReadFunc(void *opaque, uint32_t offset, int size_log2);

#define DEVIO_SIZE8  (1 << 0)
#define DEVIO_SIZE16 (1 << 1)
#define DEVIO_SIZE32 (1 << 2)
/* not supported, could add specific 64 bit callbacks when needed */
//#define DEVIO_SIZE64 (1 << 3)
#define DEVIO_DISABLED (1 << 4)

#define DEVRAM_FLAG_ROM        (1 << 0) /* not writable */
#define DEVRAM_FLAG_DIRTY_BITS (1 << 1) /* maintain dirty bits */
#define DEVRAM_FLAG_DISABLED   (1 << 2) /* allocated but not mapped */
#define DEVRAM_PAGE_SIZE_LOG2 12
#define DEVRAM_PAGE_SIZE (1 << DEVRAM_PAGE_SIZE_LOG2)

typedef struct PhysMemoryMap PhysMemoryMap;

typedef struct {
    PhysMemoryMap *map;
    uint64_t addr;
    uint64_t org_size; /* original size */
    uint64_t size; /* =org_size or 0 if the mapping is disabled */
    BOOL is_ram;
    /* the following is used for RAM access */
    int devram_flags;
    uint8_t *phys_mem;
    int dirty_bits_size; /* in bytes */
    uint32_t *dirty_bits; /* NULL if not used */
    uint32_t *dirty_bits_tab[2];
    int dirty_bits_index; /* 0-1 */
    /* the following is used for I/O access */
    void *opaque;
    DeviceReadFunc *read_func;
    DeviceWriteFunc *write_func;
    int devio_flags;
} PhysMemoryRange;

#define PHYS_MEM_RANGE_MAX 32

struct PhysMemoryMap {
    int n_phys_mem_range;
    PhysMemoryRange phys_mem_range[PHYS_MEM_RANGE_MAX];
    PhysMemoryRange *(*register_ram)(PhysMemoryMap *s, uint64_t addr,
                                     uint64_t size, int devram_flags);
    void (*free_ram)(PhysMemoryMap *s, PhysMemoryRange *pr);
    const uint32_t *(*get_dirty_bits)(PhysMemoryMap *s, PhysMemoryRange *pr);
    void (*set_ram_addr)(PhysMemoryMap *s, PhysMemoryRange *pr, uint64_t addr,
                         BOOL enabled);
    void *opaque;
    void (*flush_tlb_write_range)(void *opaque, uint8_t *ram_addr,
                                  size_t ram_size);
};

PhysMemoryMap *phys_mem_map_init(void);
void phys_mem_map_end(PhysMemoryMap *s);
PhysMemoryRange *register_ram_entry(PhysMemoryMap *s, uint64_t addr,
                                    uint64_t size, int devram_flags);
static inline PhysMemoryRange *cpu_register_ram(PhysMemoryMap *s, uint64_t addr,
                                  uint64_t size, int devram_flags)
{
    return s->register_ram(s, addr, size, devram_flags);
}
PhysMemoryRange *cpu_register_device(PhysMemoryMap *s, uint64_t addr,
                                     uint64_t size, void *opaque,
                                     DeviceReadFunc *read_func, DeviceWriteFunc *write_func,
                                     int devio_flags);
PhysMemoryRange *get_phys_mem_range(PhysMemoryMap *s, uint64_t paddr);
void phys_mem_set_addr(PhysMemoryRange *pr, uint64_t addr, BOOL enabled);

static inline const uint32_t *phys_mem_get_dirty_bits(PhysMemoryRange *pr)
{
    PhysMemoryMap *map = pr->map;
    return map->get_dirty_bits(map, pr);
}

static inline void phys_mem_set_dirty_bit(PhysMemoryRange *pr, size_t offset)
{
    size_t page_index;
    uint32_t mask, *dirty_bits_ptr;
    if (pr->dirty_bits) {
        page_index = offset >> DEVRAM_PAGE_SIZE_LOG2;
        mask = 1 << (page_index & 0x1f);
        dirty_bits_ptr = pr->dirty_bits + (page_index >> 5);
        *dirty_bits_ptr |= mask;
    }
}

static inline BOOL phys_mem_is_dirty_bit(PhysMemoryRange *pr, size_t offset)
{
    size_t page_index;
    uint32_t *dirty_bits_ptr;
    if (!pr->dirty_bits)
        return TRUE;
    page_index = offset >> DEVRAM_PAGE_SIZE_LOG2;
    dirty_bits_ptr = pr->dirty_bits + (page_index >> 5);
    return (*dirty_bits_ptr >> (page_index & 0x1f)) & 1;
}

/* IRQ support */

typedef void SetIRQFunc(void *opaque, int irq_num, int level);

typedef struct {
    SetIRQFunc *set_irq;
    void *opaque;
    int irq_num;
} IRQSignal;

void irq_init(IRQSignal *irq, SetIRQFunc *set_irq, void *opaque, int irq_num);

static inline void set_irq(IRQSignal *irq, int level)
{
    irq->set_irq(irq->opaque, irq->irq_num, level);
}

#endif /* IOMEM_H */
