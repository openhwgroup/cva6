/*
 * VIRTIO driver
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
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>
#include <stdarg.h>

#include "cutils.h"
#include "list.h"
#include "virtio.h"

#define DEBUG_VIRTIO

/* MMIO addresses - from the Linux kernel */
#define VIRTIO_MMIO_MAGIC_VALUE         0x000
#define VIRTIO_MMIO_VERSION             0x004
#define VIRTIO_MMIO_DEVICE_ID           0x008
#define VIRTIO_MMIO_VENDOR_ID           0x00c
#define VIRTIO_MMIO_DEVICE_FEATURES     0x010
#define VIRTIO_MMIO_DEVICE_FEATURES_SEL 0x014
#define VIRTIO_MMIO_DRIVER_FEATURES     0x020
#define VIRTIO_MMIO_DRIVER_FEATURES_SEL 0x024
#define VIRTIO_MMIO_GUEST_PAGE_SIZE     0x028 /* version 1 only */
#define VIRTIO_MMIO_QUEUE_SEL           0x030
#define VIRTIO_MMIO_QUEUE_NUM_MAX       0x034
#define VIRTIO_MMIO_QUEUE_NUM           0x038
#define VIRTIO_MMIO_QUEUE_ALIGN         0x03c /* version 1 only */
#define VIRTIO_MMIO_QUEUE_PFN           0x040 /* version 1 only */
#define VIRTIO_MMIO_QUEUE_READY         0x044
#define VIRTIO_MMIO_QUEUE_NOTIFY        0x050
#define VIRTIO_MMIO_INTERRUPT_STATUS    0x060
#define VIRTIO_MMIO_INTERRUPT_ACK       0x064
#define VIRTIO_MMIO_STATUS              0x070
#define VIRTIO_MMIO_QUEUE_DESC_LOW      0x080
#define VIRTIO_MMIO_QUEUE_DESC_HIGH     0x084
#define VIRTIO_MMIO_QUEUE_AVAIL_LOW     0x090
#define VIRTIO_MMIO_QUEUE_AVAIL_HIGH    0x094
#define VIRTIO_MMIO_QUEUE_USED_LOW      0x0a0
#define VIRTIO_MMIO_QUEUE_USED_HIGH     0x0a4
#define VIRTIO_MMIO_CONFIG_GENERATION   0x0fc
#define VIRTIO_MMIO_CONFIG              0x100

/* PCI registers */
#define VIRTIO_PCI_DEVICE_FEATURE_SEL   0x000
#define VIRTIO_PCI_DEVICE_FEATURE       0x004
#define VIRTIO_PCI_GUEST_FEATURE_SEL    0x008
#define VIRTIO_PCI_GUEST_FEATURE        0x00c
#define VIRTIO_PCI_MSIX_CONFIG          0x010
#define VIRTIO_PCI_NUM_QUEUES           0x012
#define VIRTIO_PCI_DEVICE_STATUS        0x014
#define VIRTIO_PCI_CONFIG_GENERATION    0x015
#define VIRTIO_PCI_QUEUE_SEL            0x016
#define VIRTIO_PCI_QUEUE_SIZE           0x018
#define VIRTIO_PCI_QUEUE_MSIX_VECTOR    0x01a
#define VIRTIO_PCI_QUEUE_ENABLE         0x01c
#define VIRTIO_PCI_QUEUE_NOTIFY_OFF     0x01e
#define VIRTIO_PCI_QUEUE_DESC_LOW       0x020
#define VIRTIO_PCI_QUEUE_DESC_HIGH      0x024
#define VIRTIO_PCI_QUEUE_AVAIL_LOW      0x028
#define VIRTIO_PCI_QUEUE_AVAIL_HIGH     0x02c
#define VIRTIO_PCI_QUEUE_USED_LOW       0x030
#define VIRTIO_PCI_QUEUE_USED_HIGH      0x034

#define VIRTIO_PCI_CFG_OFFSET          0x0000
#define VIRTIO_PCI_ISR_OFFSET          0x1000
#define VIRTIO_PCI_CONFIG_OFFSET       0x2000
#define VIRTIO_PCI_NOTIFY_OFFSET       0x3000

#define VIRTIO_PCI_CAP_LEN 16

#define MAX_QUEUE 8
#define MAX_CONFIG_SPACE_SIZE 256
#define MAX_QUEUE_NUM 16

typedef struct {
    uint32_t ready; /* 0 or 1 */
    uint32_t num;
    uint16_t last_avail_idx;
    virtio_phys_addr_t desc_addr;
    virtio_phys_addr_t avail_addr;
    virtio_phys_addr_t used_addr;
    BOOL manual_recv; /* if TRUE, the device_recv() callback is not called */
} QueueState;

#define VRING_DESC_F_NEXT       1
#define VRING_DESC_F_WRITE      2
#define VRING_DESC_F_INDIRECT   4

typedef struct {
    uint64_t addr;
    uint32_t len;
    uint16_t flags; /* VRING_DESC_F_x */
    uint16_t next;
} VIRTIODesc;

/* return < 0 to stop the notification (it must be manually restarted
   later), 0 if OK */
typedef int VIRTIODeviceRecvFunc(VIRTIODevice *s1, int queue_idx,
                                 int desc_idx, int read_size,
                                 int write_size);

/* return NULL if no RAM at this address. The mapping is valid for one page */
typedef uint8_t *VIRTIOGetRAMPtrFunc(VIRTIODevice *s, virtio_phys_addr_t paddr);

struct VIRTIODevice {
    PhysMemoryMap *mem_map;
    PhysMemoryRange *mem_range;
    /* PCI only */
    PCIDevice *pci_dev;
    /* MMIO only */
    IRQSignal *irq;
    VIRTIOGetRAMPtrFunc *get_ram_ptr;
    int debug;

    uint32_t int_status;
    uint32_t status;
    uint32_t device_features_sel;
    uint32_t queue_sel; /* currently selected queue */
    QueueState queue[MAX_QUEUE];

    /* device specific */
    uint32_t device_id;
    uint32_t vendor_id;
    uint32_t device_features;
    VIRTIODeviceRecvFunc *device_recv;
    void (*config_write)(VIRTIODevice *s); /* called after the config
                                              is written */
    uint32_t config_space_size; /* in bytes, must be multiple of 4 */
    uint8_t config_space[MAX_CONFIG_SPACE_SIZE];
};

static uint32_t virtio_mmio_read(void *opaque, uint32_t offset1, int size_log2);
static void virtio_mmio_write(void *opaque, uint32_t offset,
                              uint32_t val, int size_log2);
static uint32_t virtio_pci_read(void *opaque, uint32_t offset, int size_log2);
static void virtio_pci_write(void *opaque, uint32_t offset,
                             uint32_t val, int size_log2);

static void virtio_reset(VIRTIODevice *s)
{
    int i;

    s->status = 0;
    s->queue_sel = 0;
    s->device_features_sel = 0;
    s->int_status = 0;
    for (i = 0; i < MAX_QUEUE; i++) {
        QueueState *qs = &s->queue[i];
        qs->ready = 0;
        qs->num = MAX_QUEUE_NUM;
        qs->desc_addr = 0;
        qs->avail_addr = 0;
        qs->used_addr = 0;
        qs->last_avail_idx = 0;
    }
}

static uint8_t *virtio_pci_get_ram_ptr(VIRTIODevice *s, virtio_phys_addr_t paddr)
{
    return pci_device_get_dma_ptr(s->pci_dev, paddr);
}

static uint8_t *virtio_mmio_get_ram_ptr(VIRTIODevice *s, virtio_phys_addr_t paddr)
{
    PhysMemoryRange *pr;

    pr = get_phys_mem_range(s->mem_map, paddr);
    if (!pr || !pr->is_ram)
        return NULL;
    return pr->phys_mem + (uintptr_t)(paddr - pr->addr);
}

static void virtio_add_pci_capability(VIRTIODevice *s, int cfg_type,
                                      int bar, uint32_t offset, uint32_t len,
                                      uint32_t mult)
{
    uint8_t cap[20];
    int cap_len;
    if (cfg_type == 2)
        cap_len = 20;
    else
        cap_len = 16;
    memset(cap, 0, cap_len);
    cap[0] = 0x09; /* vendor specific */
    cap[2] = cap_len; /* set by pci_add_capability() */
    cap[3] = cfg_type;
    cap[4] = bar;
    put_le32(cap + 8, offset);
    put_le32(cap + 12, len);
    if (cfg_type == 2)
        put_le32(cap + 16, mult);
    pci_add_capability(s->pci_dev, cap, cap_len);
}

static void virtio_pci_bar_set(void *opaque, int bar_num,
                               uint32_t addr, BOOL enabled)
{
    VIRTIODevice *s = (VIRTIODevice *)opaque;
    phys_mem_set_addr(s->mem_range, addr, enabled);
}

static void virtio_init(VIRTIODevice *s, VIRTIOBusDef *bus,
                        uint32_t device_id, int config_space_size,
                        VIRTIODeviceRecvFunc *device_recv)
{
    memset(s, 0, sizeof(*s));

    if (bus->pci_bus) {
        uint16_t pci_device_id, class_id;
        char name[32];
        int bar_num;

        switch (device_id) {
        case 1:
            pci_device_id = 0x1000; /* net */
            class_id = 0x0200;
            break;
        case 2:
            pci_device_id = 0x1001; /* block */
            class_id = 0x0100; /* XXX: check it */
            break;
        case 3:
            pci_device_id = 0x1003; /* console */
            class_id = 0x0780;
            break;
        case 9:
            pci_device_id = 0x1040 + device_id; /* use new device ID */
            class_id = 0x2;
            break;
        case 18:
            pci_device_id = 0x1040 + device_id; /* use new device ID */
            class_id = 0x0980;
            break;
        default:
            abort();
        }
        snprintf(name, sizeof(name), "virtio_%04x", pci_device_id);
        s->pci_dev = pci_register_device(bus->pci_bus, name, -1,
                                         0x1af4, pci_device_id, 0x00,
                                         class_id);
        pci_device_set_config16(s->pci_dev, 0x2c, 0x1af4);
        pci_device_set_config16(s->pci_dev, 0x2e, device_id);
        pci_device_set_config8(s->pci_dev, PCI_INTERRUPT_PIN, 1);

        bar_num = 4;
        virtio_add_pci_capability(s, 1, bar_num,
                              VIRTIO_PCI_CFG_OFFSET, 0x1000, 0); /* common */
        virtio_add_pci_capability(s, 3, bar_num,
                              VIRTIO_PCI_ISR_OFFSET, 0x1000, 0); /* isr */
        virtio_add_pci_capability(s, 4, bar_num,
                              VIRTIO_PCI_CONFIG_OFFSET, 0x1000, 0); /* config */
        virtio_add_pci_capability(s, 2, bar_num,
                              VIRTIO_PCI_NOTIFY_OFFSET, 0x1000, 0); /* notify */

        s->get_ram_ptr = virtio_pci_get_ram_ptr;
        s->irq = pci_device_get_irq(s->pci_dev, 0);
        s->mem_map = pci_device_get_mem_map(s->pci_dev);
        s->mem_range = cpu_register_device(s->mem_map, 0, 0x4000, s,
                                           virtio_pci_read, virtio_pci_write,
                                           DEVIO_SIZE8 | DEVIO_SIZE16 | DEVIO_SIZE32 | DEVIO_DISABLED);
        pci_register_bar(s->pci_dev, bar_num, 0x4000, PCI_ADDRESS_SPACE_MEM,
                         s, virtio_pci_bar_set);
    } else {
        /* MMIO case */
        s->mem_map = bus->mem_map;
        s->irq = bus->irq;
        s->mem_range = cpu_register_device(s->mem_map, bus->addr, VIRTIO_PAGE_SIZE,
                                           s, virtio_mmio_read, virtio_mmio_write,
                                           DEVIO_SIZE8 | DEVIO_SIZE16 | DEVIO_SIZE32);
        s->get_ram_ptr = virtio_mmio_get_ram_ptr;
    }

    s->device_id = device_id;
    s->vendor_id = 0xffff;
    s->config_space_size = config_space_size;
    s->device_recv = device_recv;
    virtio_reset(s);
}

static uint16_t virtio_read16(VIRTIODevice *s, virtio_phys_addr_t addr)
{
    uint8_t *ptr;
    if (addr & 1)
        return 0; /* unaligned access are not supported */
    ptr = s->get_ram_ptr(s, addr);
    if (!ptr)
        return 0;
    return *(uint16_t *)ptr;
}

static void virtio_write16(VIRTIODevice *s, virtio_phys_addr_t addr,
                           uint16_t val)
{
    uint8_t *ptr;
    if (addr & 1)
        return; /* unaligned access are not supported */
    ptr = s->get_ram_ptr(s, addr);
    if (!ptr)
        return;
    *(uint16_t *)ptr = val;
}

static void virtio_write32(VIRTIODevice *s, virtio_phys_addr_t addr,
                           uint32_t val)
{
    uint8_t *ptr;
    if (addr & 3)
        return; /* unaligned access are not supported */
    ptr = s->get_ram_ptr(s, addr);
    if (!ptr)
        return;
    *(uint32_t *)ptr = val;
}

static int virtio_memcpy_from_ram(VIRTIODevice *s, uint8_t *buf,
                                  virtio_phys_addr_t addr, int count)
{
    uint8_t *ptr;
    int l;

    while (count > 0) {
        l = min_int(count, VIRTIO_PAGE_SIZE - (addr & (VIRTIO_PAGE_SIZE - 1)));
        ptr = s->get_ram_ptr(s, addr);
        if (!ptr)
            return -1;
        memcpy(buf, ptr, l);
        addr += l;
        buf += l;
        count -= l;
    }
    return 0;
}

static int virtio_memcpy_to_ram(VIRTIODevice *s, virtio_phys_addr_t addr,
                                const uint8_t *buf, int count)
{
    uint8_t *ptr;
    int l;

    while (count > 0) {
        l = min_int(count, VIRTIO_PAGE_SIZE - (addr & (VIRTIO_PAGE_SIZE - 1)));
        ptr = s->get_ram_ptr(s, addr);
        if (!ptr)
            return -1;
        memcpy(ptr, buf, l);
        addr += l;
        buf += l;
        count -= l;
    }
    return 0;
}

static int get_desc(VIRTIODevice *s, VIRTIODesc *desc,
                    int queue_idx, int desc_idx)
{
    QueueState *qs = &s->queue[queue_idx];
    return virtio_memcpy_from_ram(s, (uint8_t *)desc, qs->desc_addr +
                                  desc_idx * sizeof(VIRTIODesc),
                                  sizeof(VIRTIODesc));
}

static int memcpy_to_from_queue(VIRTIODevice *s, uint8_t *buf,
                                int queue_idx, int desc_idx,
                                int offset, int count, BOOL to_queue)
{
    VIRTIODesc desc;
    int l, f_write_flag;

    if (count == 0)
        return 0;

    get_desc(s, &desc, queue_idx, desc_idx);

    if (to_queue) {
        f_write_flag = VRING_DESC_F_WRITE;
        /* find the first write descriptor */
        for (;;) {
            if ((desc.flags & VRING_DESC_F_WRITE) == f_write_flag)
                break;
            if (!(desc.flags & VRING_DESC_F_NEXT))
                return -1;
            desc_idx = desc.next;
            get_desc(s, &desc, queue_idx, desc_idx);
        }
    } else {
        f_write_flag = 0;
    }

    /* find the descriptor at offset */
    for (;;) {
        if ((desc.flags & VRING_DESC_F_WRITE) != f_write_flag)
            return -1;
        if (offset < (int)desc.len)
            break;
        if (!(desc.flags & VRING_DESC_F_NEXT))
            return -1;
        desc_idx = desc.next;
        offset -= desc.len;
        get_desc(s, &desc, queue_idx, desc_idx);
    }

    for (;;) {
        l = min_int(count, desc.len - offset);
        if (to_queue)
            virtio_memcpy_to_ram(s, desc.addr + offset, buf, l);
        else
            virtio_memcpy_from_ram(s, buf, desc.addr + offset, l);
        count -= l;
        if (count == 0)
            break;
        offset += l;
        buf += l;
        if (offset == (int)desc.len) {
            if (!(desc.flags & VRING_DESC_F_NEXT))
                return -1;
            desc_idx = desc.next;
            get_desc(s, &desc, queue_idx, desc_idx);
            if ((desc.flags & VRING_DESC_F_WRITE) != f_write_flag)
                return -1;
            offset = 0;
        }
    }
    return 0;
}

static int memcpy_from_queue(VIRTIODevice *s, void *buf,
                             int queue_idx, int desc_idx,
                             int offset, int count)
{
    return memcpy_to_from_queue(s, (uint8_t *)buf, queue_idx, desc_idx, offset, count,
                                FALSE);
}

static int memcpy_to_queue(VIRTIODevice *s,
                           int queue_idx, int desc_idx,
                           int offset, const void *buf, int count)
{
    return memcpy_to_from_queue(s, (uint8_t *)buf, queue_idx, desc_idx, offset,
                                count, TRUE);
}

/* signal that the descriptor has been consumed */
static void virtio_consume_desc(VIRTIODevice *s,
                                int queue_idx, int desc_idx, int desc_len)
{
    QueueState *qs = &s->queue[queue_idx];
    virtio_phys_addr_t addr;
    uint32_t index;

    addr = qs->used_addr + 2;
    index = virtio_read16(s, addr);
    virtio_write16(s, addr, index + 1);

    addr = qs->used_addr + 4 + (index & (qs->num - 1)) * 8;
    virtio_write32(s, addr, desc_idx);
    virtio_write32(s, addr + 4, desc_len);

    s->int_status |= 1;
    set_irq(s->irq, 1);
}

static int get_desc_rw_size(VIRTIODevice *s,
                             int *pread_size, int *pwrite_size,
                             int queue_idx, int desc_idx)
{
    VIRTIODesc desc;
    int read_size, write_size;

    read_size = 0;
    write_size = 0;
    get_desc(s, &desc, queue_idx, desc_idx);

    for (;;) {
        if (desc.flags & VRING_DESC_F_WRITE)
            break;
        read_size += desc.len;
        if (!(desc.flags & VRING_DESC_F_NEXT))
            goto done;
        desc_idx = desc.next;
        get_desc(s, &desc, queue_idx, desc_idx);
    }

    for (;;) {
        if (!(desc.flags & VRING_DESC_F_WRITE))
            return -1;
        write_size += desc.len;
        if (!(desc.flags & VRING_DESC_F_NEXT))
            break;
        desc_idx = desc.next;
        get_desc(s, &desc, queue_idx, desc_idx);
    }

 done:
    *pread_size = read_size;
    *pwrite_size = write_size;
    return 0;
}

/* XXX: test if the queue is ready ? */
static void queue_notify(VIRTIODevice *s, int queue_idx)
{
    QueueState *qs = &s->queue[queue_idx];
    uint16_t avail_idx;
    int desc_idx, read_size, write_size;

    if (qs->manual_recv)
        return;

    avail_idx = virtio_read16(s, qs->avail_addr + 2);
    while (qs->last_avail_idx != avail_idx) {
        desc_idx = virtio_read16(s, qs->avail_addr + 4 +
                                 (qs->last_avail_idx & (qs->num - 1)) * 2);
        if (!get_desc_rw_size(s, &read_size, &write_size, queue_idx, desc_idx)) {
#ifdef DEBUG_VIRTIO
            if (s->debug & VIRTIO_DEBUG_IO) {
                printf("queue_notify: idx=%d read_size=%d write_size=%d\n",
                       queue_idx, read_size, write_size);
            }
#endif
            if (s->device_recv(s, queue_idx, desc_idx,
                               read_size, write_size) < 0)
                break;
        }
        qs->last_avail_idx++;
    }
}

static uint32_t virtio_config_read(VIRTIODevice *s, uint32_t offset,
                                   int size_log2)
{
    uint32_t val;
    switch (size_log2) {
    case 0:
        if (offset < s->config_space_size) {
            val = s->config_space[offset];
        } else {
            val = 0;
        }
        break;
    case 1:
        if (offset < (s->config_space_size - 1)) {
            val = get_le16(&s->config_space[offset]);
        } else {
            val = 0;
        }
        break;
    case 2:
        if (offset < (s->config_space_size - 3)) {
            val = get_le32(s->config_space + offset);
        } else {
            val = 0;
        }
        break;
    default:
        abort();
    }
    return val;
}

static void virtio_config_write(VIRTIODevice *s, uint32_t offset,
                                uint32_t val, int size_log2)
{
    switch (size_log2) {
    case 0:
        if (offset < s->config_space_size) {
            s->config_space[offset] = val;
            if (s->config_write)
                s->config_write(s);
        }
        break;
    case 1:
        if (offset < s->config_space_size - 1) {
            put_le16(s->config_space + offset, val);
            if (s->config_write)
                s->config_write(s);
        }
        break;
    case 2:
        if (offset < s->config_space_size - 3) {
            put_le32(s->config_space + offset, val);
            if (s->config_write)
                s->config_write(s);
        }
        break;
    }
}

static uint32_t virtio_mmio_read(void *opaque, uint32_t offset, int size_log2)
{
    VIRTIODevice *s = (VIRTIODevice *)opaque;
    uint32_t val;

    if (offset >= VIRTIO_MMIO_CONFIG) {
        return virtio_config_read(s, offset - VIRTIO_MMIO_CONFIG, size_log2);
    }

    if (size_log2 == 2) {
        switch (offset) {
        case VIRTIO_MMIO_MAGIC_VALUE:
            val = 0x74726976;
            break;
        case VIRTIO_MMIO_VERSION:
            val = 2;
            break;
        case VIRTIO_MMIO_DEVICE_ID:
            val = s->device_id;
            break;
        case VIRTIO_MMIO_VENDOR_ID:
            val = s->vendor_id;
            break;
        case VIRTIO_MMIO_DEVICE_FEATURES:
            switch (s->device_features_sel) {
            case 0:
                val = s->device_features;
                break;
            case 1:
                val = 1; /* version 1 */
                break;
            default:
                val = 0;
                break;
            }
            break;
        case VIRTIO_MMIO_DEVICE_FEATURES_SEL:
            val = s->device_features_sel;
            break;
        case VIRTIO_MMIO_QUEUE_SEL:
            val = s->queue_sel;
            break;
        case VIRTIO_MMIO_QUEUE_NUM_MAX:
            val = MAX_QUEUE_NUM;
            break;
        case VIRTIO_MMIO_QUEUE_NUM:
            val = s->queue[s->queue_sel].num;
            break;
        case VIRTIO_MMIO_QUEUE_DESC_LOW:
            val = s->queue[s->queue_sel].desc_addr;
            break;
        case VIRTIO_MMIO_QUEUE_AVAIL_LOW:
            val = s->queue[s->queue_sel].avail_addr;
            break;
        case VIRTIO_MMIO_QUEUE_USED_LOW:
            val = s->queue[s->queue_sel].used_addr;
            break;
        case VIRTIO_MMIO_QUEUE_DESC_HIGH:
            val = s->queue[s->queue_sel].desc_addr >> 32;
            break;
        case VIRTIO_MMIO_QUEUE_AVAIL_HIGH:
            val = s->queue[s->queue_sel].avail_addr >> 32;
            break;
        case VIRTIO_MMIO_QUEUE_USED_HIGH:
            val = s->queue[s->queue_sel].used_addr >> 32;
            break;
        case VIRTIO_MMIO_QUEUE_READY:
            val = s->queue[s->queue_sel].ready;
            break;
        case VIRTIO_MMIO_INTERRUPT_STATUS:
            val = s->int_status;
            break;
        case VIRTIO_MMIO_STATUS:
            val = s->status;
            break;
        case VIRTIO_MMIO_CONFIG_GENERATION:
            val = 0;
            break;
        default:
            val = 0;
            break;
        }
    } else {
        val = 0;
    }
#ifdef DEBUG_VIRTIO
    if (s->debug & VIRTIO_DEBUG_IO) {
        printf("virto_mmio_read: offset=0x%x val=0x%x size=%d\n",
               offset, val, 1 << size_log2);
    }
#endif
    return val;
}

static void set_low32(virtio_phys_addr_t *paddr, uint32_t val)
{
    *paddr = (*paddr & ~(virtio_phys_addr_t)0xffffffff) | val;
}

static void set_high32(virtio_phys_addr_t *paddr, uint32_t val)
{
    *paddr = (*paddr & 0xffffffff) | ((virtio_phys_addr_t)val << 32);
}

static void virtio_mmio_write(void *opaque, uint32_t offset,
                              uint32_t val, int size_log2)
{
    VIRTIODevice *s = (VIRTIODevice *)opaque;

#ifdef DEBUG_VIRTIO
    if (s->debug & VIRTIO_DEBUG_IO) {
        printf("virto_mmio_write: offset=0x%x val=0x%x size=%d\n",
               offset, val, 1 << size_log2);
    }
#endif

    if (offset >= VIRTIO_MMIO_CONFIG) {
        virtio_config_write(s, offset - VIRTIO_MMIO_CONFIG, val, size_log2);
        return;
    }

    if (size_log2 == 2) {
        switch (offset) {
        case VIRTIO_MMIO_DEVICE_FEATURES_SEL:
            s->device_features_sel = val;
            break;
        case VIRTIO_MMIO_QUEUE_SEL:
            if (val < MAX_QUEUE)
                s->queue_sel = val;
            break;
        case VIRTIO_MMIO_QUEUE_NUM:
            if ((val & (val - 1)) == 0 && val > 0) {
                s->queue[s->queue_sel].num = val;
            }
            break;
        case VIRTIO_MMIO_QUEUE_DESC_LOW:
            set_low32(&s->queue[s->queue_sel].desc_addr, val);
            break;
        case VIRTIO_MMIO_QUEUE_AVAIL_LOW:
            set_low32(&s->queue[s->queue_sel].avail_addr, val);
            break;
        case VIRTIO_MMIO_QUEUE_USED_LOW:
            set_low32(&s->queue[s->queue_sel].used_addr, val);
            break;
        case VIRTIO_MMIO_QUEUE_DESC_HIGH:
            set_high32(&s->queue[s->queue_sel].desc_addr, val);
            break;
        case VIRTIO_MMIO_QUEUE_AVAIL_HIGH:
            set_high32(&s->queue[s->queue_sel].avail_addr, val);
            break;
        case VIRTIO_MMIO_QUEUE_USED_HIGH:
            set_high32(&s->queue[s->queue_sel].used_addr, val);
            break;
        case VIRTIO_MMIO_STATUS:
            s->status = val;
            if (val == 0) {
                /* reset */
                set_irq(s->irq, 0);
                virtio_reset(s);
            }
            break;
        case VIRTIO_MMIO_QUEUE_READY:
            s->queue[s->queue_sel].ready = val & 1;
            break;
        case VIRTIO_MMIO_QUEUE_NOTIFY:
            if (val < MAX_QUEUE)
                queue_notify(s, val);
            break;
        case VIRTIO_MMIO_INTERRUPT_ACK:
            s->int_status &= ~val;
            if (s->int_status == 0) {
                set_irq(s->irq, 0);
            }
            break;
        }
    }
}

static uint32_t virtio_pci_read(void *opaque, uint32_t offset1, int size_log2)
{
    VIRTIODevice *s = (VIRTIODevice *)opaque;
    uint32_t offset;
    uint32_t val = 0;

    offset = offset1 & 0xfff;
    switch (offset1 >> 12) {
    case VIRTIO_PCI_CFG_OFFSET >> 12:
        if (size_log2 == 2) {
            switch (offset) {
            case VIRTIO_PCI_DEVICE_FEATURE:
                switch (s->device_features_sel) {
                case 0:
                    val = s->device_features;
                    break;
                case 1:
                    val = 1; /* version 1 */
                    break;
                default:
                    val = 0;
                    break;
                }
                break;
            case VIRTIO_PCI_DEVICE_FEATURE_SEL:
                val = s->device_features_sel;
                break;
            case VIRTIO_PCI_QUEUE_DESC_LOW:
                val = s->queue[s->queue_sel].desc_addr;
                break;
            case VIRTIO_PCI_QUEUE_AVAIL_LOW:
                val = s->queue[s->queue_sel].avail_addr;
                break;
            case VIRTIO_PCI_QUEUE_USED_LOW:
                val = s->queue[s->queue_sel].used_addr;
                break;
            case VIRTIO_PCI_QUEUE_DESC_HIGH:
                val = s->queue[s->queue_sel].desc_addr >> 32;
                break;
            case VIRTIO_PCI_QUEUE_AVAIL_HIGH:
                val = s->queue[s->queue_sel].avail_addr >> 32;
                break;
            case VIRTIO_PCI_QUEUE_USED_HIGH:
                val = s->queue[s->queue_sel].used_addr >> 32;
                break;
            }
        } else if (size_log2 == 1) {
            switch (offset) {
            case VIRTIO_PCI_NUM_QUEUES:
                val = MAX_QUEUE_NUM;
                break;
            case VIRTIO_PCI_QUEUE_SEL:
                val = s->queue_sel;
                break;
            case VIRTIO_PCI_QUEUE_SIZE:
                val = s->queue[s->queue_sel].num;
                break;
            case VIRTIO_PCI_QUEUE_ENABLE:
                val = s->queue[s->queue_sel].ready;
                break;
            case VIRTIO_PCI_QUEUE_NOTIFY_OFF:
                val = 0;
                break;
            }
        } else if (size_log2 == 0) {
            switch (offset) {
            case VIRTIO_PCI_DEVICE_STATUS:
                val = s->status;
                break;
            }
        }
        break;
    case VIRTIO_PCI_ISR_OFFSET >> 12:
        if (offset == 0 && size_log2 == 0) {
            val = s->int_status;
            s->int_status = 0;
            set_irq(s->irq, 0);
        }
        break;
    case VIRTIO_PCI_CONFIG_OFFSET >> 12:
        val = virtio_config_read(s, offset, size_log2);
        break;
    }
#ifdef DEBUG_VIRTIO
    if (s->debug & VIRTIO_DEBUG_IO) {
        printf("virto_pci_read: offset=0x%x val=0x%x size=%d\n",
               offset1, val, 1 << size_log2);
    }
#endif
    return val;
}

static void virtio_pci_write(void *opaque, uint32_t offset1,
                             uint32_t val, int size_log2)
{
    VIRTIODevice *s = (VIRTIODevice *)opaque;
    uint32_t offset;

#ifdef DEBUG_VIRTIO
    if (s->debug & VIRTIO_DEBUG_IO) {
        printf("virto_pci_write: offset=0x%x val=0x%x size=%d\n",
               offset1, val, 1 << size_log2);
    }
#endif
    offset = offset1 & 0xfff;
    switch (offset1 >> 12) {
    case VIRTIO_PCI_CFG_OFFSET >> 12:
        if (size_log2 == 2) {
            switch (offset) {
            case VIRTIO_PCI_DEVICE_FEATURE_SEL:
                s->device_features_sel = val;
                break;
            case VIRTIO_PCI_QUEUE_DESC_LOW:
                set_low32(&s->queue[s->queue_sel].desc_addr, val);
                break;
            case VIRTIO_PCI_QUEUE_AVAIL_LOW:
                set_low32(&s->queue[s->queue_sel].avail_addr, val);
                break;
            case VIRTIO_PCI_QUEUE_USED_LOW:
                set_low32(&s->queue[s->queue_sel].used_addr, val);
                break;
            case VIRTIO_PCI_QUEUE_DESC_HIGH:
                set_high32(&s->queue[s->queue_sel].desc_addr, val);
                break;
            case VIRTIO_PCI_QUEUE_AVAIL_HIGH:
                set_high32(&s->queue[s->queue_sel].avail_addr, val);
                break;
            case VIRTIO_PCI_QUEUE_USED_HIGH:
                set_high32(&s->queue[s->queue_sel].used_addr, val);
                break;
            }
        } else if (size_log2 == 1) {
            switch (offset) {
            case VIRTIO_PCI_QUEUE_SEL:
                if (val < MAX_QUEUE)
                    s->queue_sel = val;
                break;
            case VIRTIO_PCI_QUEUE_SIZE:
                if ((val & (val - 1)) == 0 && val > 0) {
                    s->queue[s->queue_sel].num = val;
                }
                break;
            case VIRTIO_PCI_QUEUE_ENABLE:
                s->queue[s->queue_sel].ready = val & 1;
                break;
            }
        } else if (size_log2 == 0) {
            switch (offset) {
            case VIRTIO_PCI_DEVICE_STATUS:
                s->status = val;
                if (val == 0) {
                    /* reset */
                    set_irq(s->irq, 0);
                    virtio_reset(s);
                }
                break;
            }
        }
        break;
    case VIRTIO_PCI_CONFIG_OFFSET >> 12:
        virtio_config_write(s, offset, val, size_log2);
        break;
    case VIRTIO_PCI_NOTIFY_OFFSET >> 12:
        if (val < MAX_QUEUE)
            queue_notify(s, val);
        break;
    }
}

void virtio_set_debug(VIRTIODevice *s, int debug)
{
    s->debug = debug;
}

static void virtio_config_change_notify(VIRTIODevice *s)
{
    /* INT_CONFIG interrupt */
    s->int_status |= 2;
    set_irq(s->irq, 1);
}

/*********************************************************************/
/* block device */

typedef struct {
    uint32_t type;
    uint8_t *buf;
    int write_size;
    int queue_idx;
    int desc_idx;
} BlockRequest;

typedef struct VIRTIOBlockDevice {
    VIRTIODevice common;
    BlockDevice *bs;

    BOOL req_in_progress;
    BlockRequest req; /* request in progress */
} VIRTIOBlockDevice;

typedef struct {
    uint32_t type;
    uint32_t ioprio;
    uint64_t sector_num;
} BlockRequestHeader;

#define VIRTIO_BLK_T_IN          0
#define VIRTIO_BLK_T_OUT         1
#define VIRTIO_BLK_T_FLUSH       4
#define VIRTIO_BLK_T_FLUSH_OUT   5

#define VIRTIO_BLK_S_OK     0
#define VIRTIO_BLK_S_IOERR  1
#define VIRTIO_BLK_S_UNSUPP 2

#define SECTOR_SIZE 512

static void virtio_block_req_end(VIRTIODevice *s, int ret)
{
    VIRTIOBlockDevice *s1 = (VIRTIOBlockDevice *)s;
    int write_size;
    int queue_idx = s1->req.queue_idx;
    int desc_idx = s1->req.desc_idx;
    uint8_t *buf, buf1[1];

    switch (s1->req.type) {
    case VIRTIO_BLK_T_IN:
        write_size = s1->req.write_size;
        buf = s1->req.buf;
        if (ret < 0) {
            buf[write_size - 1] = VIRTIO_BLK_S_IOERR;
        } else {
            buf[write_size - 1] = VIRTIO_BLK_S_OK;
        }
        memcpy_to_queue(s, queue_idx, desc_idx, 0, buf, write_size);
        free(buf);
        virtio_consume_desc(s, queue_idx, desc_idx, write_size);
        break;
    case VIRTIO_BLK_T_OUT:
        if (ret < 0)
            buf1[0] = VIRTIO_BLK_S_IOERR;
        else
            buf1[0] = VIRTIO_BLK_S_OK;
        memcpy_to_queue(s, queue_idx, desc_idx, 0, buf1, sizeof(buf1));
        virtio_consume_desc(s, queue_idx, desc_idx, 1);
        break;
    default:
        abort();
    }
}

static void virtio_block_req_cb(void *opaque, int ret)
{
    VIRTIODevice *s = (VIRTIODevice *)opaque;
    VIRTIOBlockDevice *s1 = (VIRTIOBlockDevice *)s;

    virtio_block_req_end(s, ret);

    s1->req_in_progress = FALSE;

    /* handle next requests */
    queue_notify((VIRTIODevice *)s, s1->req.queue_idx);
}

/* XXX: handle async I/O */
static int virtio_block_recv_request(VIRTIODevice *s, int queue_idx,
                                     int desc_idx, int read_size,
                                     int write_size)
{
    VIRTIOBlockDevice *s1 = (VIRTIOBlockDevice *)s;
    BlockDevice *bs = s1->bs;
    BlockRequestHeader h;
    uint8_t *buf;
    int len, ret;

    if (s1->req_in_progress)
        return -1;

    if (memcpy_from_queue(s, &h, queue_idx, desc_idx, 0, sizeof(h)) < 0)
        return 0;
    s1->req.type = h.type;
    s1->req.queue_idx = queue_idx;
    s1->req.desc_idx = desc_idx;
    switch (h.type) {
    case VIRTIO_BLK_T_IN:
        s1->req.buf = (uint8_t *)malloc(write_size);
        s1->req.write_size = write_size;
        ret = bs->read_async(bs, h.sector_num, s1->req.buf,
                             (write_size - 1) / SECTOR_SIZE,
                             virtio_block_req_cb, s);
        if (ret > 0) {
            /* asyncronous read */
            s1->req_in_progress = TRUE;
        } else {
            virtio_block_req_end(s, ret);
        }
        break;
    case VIRTIO_BLK_T_OUT:
        assert(write_size >= 1);
        len = read_size - sizeof(h);
        buf = (uint8_t *)malloc(len);
        memcpy_from_queue(s, buf, queue_idx, desc_idx, sizeof(h), len);
        ret = bs->write_async(bs, h.sector_num, buf, len / SECTOR_SIZE,
                              virtio_block_req_cb, s);
        free(buf);
        if (ret > 0) {
            /* asyncronous write */
            s1->req_in_progress = TRUE;
        } else {
            virtio_block_req_end(s, ret);
        }
        break;
    default:
        break;
    }
    return 0;
}

VIRTIODevice *virtio_block_init(VIRTIOBusDef *bus, BlockDevice *bs)
{
    uint64_t nb_sectors;

    VIRTIOBlockDevice *s = (VIRTIOBlockDevice *)mallocz(sizeof(*s));
    virtio_init(&s->common, bus,
                2, 8, virtio_block_recv_request);
    s->bs = bs;

    nb_sectors = bs->get_sector_count(bs);
    put_le32(s->common.config_space, nb_sectors);
    put_le32(s->common.config_space + 4, nb_sectors >> 32);

    return (VIRTIODevice *)s;
}

/*********************************************************************/
/* network device */

typedef struct VIRTIONetDevice {
    VIRTIODevice common;
    EthernetDevice *es;
    int header_size;
} VIRTIONetDevice;

typedef struct {
    uint8_t flags;
    uint8_t gso_type;
    uint16_t hdr_len;
    uint16_t gso_size;
    uint16_t csum_start;
    uint16_t csum_offset;
    uint16_t num_buffers;
} VIRTIONetHeader;

static int virtio_net_recv_request(VIRTIODevice *s, int queue_idx,
                                   int desc_idx, int read_size,
                                   int write_size)
{
    VIRTIONetDevice *s1 = (VIRTIONetDevice *)s;
    EthernetDevice *es = s1->es;
    VIRTIONetHeader h;
    uint8_t *buf;
    int len;

    if (queue_idx == 1) {
        /* send to network */
        if (memcpy_from_queue(s, &h, queue_idx, desc_idx, 0, s1->header_size) < 0)
            return 0;
        len = read_size - s1->header_size;
        buf = (uint8_t *)malloc(len);
        memcpy_from_queue(s, buf, queue_idx, desc_idx, s1->header_size, len);
        es->write_packet(es, buf, len);
        free(buf);
        virtio_consume_desc(s, queue_idx, desc_idx, 0);
    }
    return 0;
}

static BOOL virtio_net_can_write_packet(EthernetDevice *es)
{
    VIRTIODevice *s = (VIRTIODevice *)es->device_opaque;
    QueueState *qs = &s->queue[0];
    uint16_t avail_idx;

    if (!qs->ready)
        return FALSE;
    avail_idx = virtio_read16(s, qs->avail_addr + 2);
    return qs->last_avail_idx != avail_idx;
}

static void virtio_net_write_packet(EthernetDevice *es, const uint8_t *buf, int buf_len)
{
    VIRTIODevice *s = (VIRTIODevice *)es->device_opaque;
    VIRTIONetDevice *s1 = (VIRTIONetDevice *)s;
    int queue_idx = 0;
    QueueState *qs = &s->queue[queue_idx];
    int desc_idx;
    VIRTIONetHeader h;
    int len, read_size, write_size;
    uint16_t avail_idx;

    if (!qs->ready)
        return;
    avail_idx = virtio_read16(s, qs->avail_addr + 2);
    if (qs->last_avail_idx == avail_idx)
        return;
    desc_idx = virtio_read16(s, qs->avail_addr + 4 +
                             (qs->last_avail_idx & (qs->num - 1)) * 2);
    if (get_desc_rw_size(s, &read_size, &write_size, queue_idx, desc_idx))
        return;
    len = s1->header_size + buf_len;
    if (len > write_size)
        return;
    memset(&h, 0, s1->header_size);
    memcpy_to_queue(s, queue_idx, desc_idx, 0, &h, s1->header_size);
    memcpy_to_queue(s, queue_idx, desc_idx, s1->header_size, buf, buf_len);
    virtio_consume_desc(s, queue_idx, desc_idx, len);
    qs->last_avail_idx++;
}

static void virtio_net_set_carrier(EthernetDevice *es, BOOL carrier_state)
{
#if 0
    VIRTIODevice *s1 = es->device_opaque;
    VIRTIONetDevice *s = (VIRTIONetDevice *)s1;
    int cur_carrier_state;

    //    printf("virtio_net_set_carrier: %d\n", carrier_state);
    cur_carrier_state = s->common.config_space[6] & 1;
    if (cur_carrier_state != carrier_state) {
        s->common.config_space[6] = (carrier_state << 0);
        virtio_config_change_notify(s1);
    }
#endif
}

VIRTIODevice *virtio_net_init(VIRTIOBusDef *bus, EthernetDevice *es)
{
    VIRTIONetDevice *s = (VIRTIONetDevice *)mallocz(sizeof(*s));

    virtio_init(&s->common, bus,
                1, 6 + 2, virtio_net_recv_request);
    /* VIRTIO_NET_F_MAC, VIRTIO_NET_F_STATUS */
    s->common.device_features = (1 << 5) /* | (1 << 16) */;
    s->common.queue[0].manual_recv = TRUE;
    s->es = es;
    memcpy(s->common.config_space, es->mac_addr, 6);
    /* status */
    s->common.config_space[6] = 0;
    s->common.config_space[7] = 0;

    s->header_size = sizeof(VIRTIONetHeader);

    es->device_opaque = s;
    es->device_can_write_packet = virtio_net_can_write_packet;
    es->device_write_packet = virtio_net_write_packet;
    es->device_set_carrier = virtio_net_set_carrier;
    return (VIRTIODevice *)s;
}

/*********************************************************************/
/* console device */

typedef struct VIRTIOConsoleDevice {
    VIRTIODevice common;
    CharacterDevice *cs;
} VIRTIOConsoleDevice;

static int virtio_console_recv_request(VIRTIODevice *s, int queue_idx,
                                       int desc_idx, int read_size,
                                       int write_size)
{
    VIRTIOConsoleDevice *s1 = (VIRTIOConsoleDevice *)s;
    CharacterDevice *cs = s1->cs;
    uint8_t *buf;

    if (queue_idx == 1) {
        /* send to console */
        buf = (uint8_t *)malloc(read_size);
        memcpy_from_queue(s, buf, queue_idx, desc_idx, 0, read_size);
        cs->write_data(cs->opaque, buf, read_size);
        free(buf);
        virtio_consume_desc(s, queue_idx, desc_idx, 0);
    }
    return 0;
}

BOOL virtio_console_can_write_data(VIRTIODevice *s)
{
    QueueState *qs = &s->queue[0];
    uint16_t avail_idx;

    if (!qs->ready)
        return FALSE;
    avail_idx = virtio_read16(s, qs->avail_addr + 2);
    return qs->last_avail_idx != avail_idx;
}

int virtio_console_get_write_len(VIRTIODevice *s)
{
    int queue_idx = 0;
    QueueState *qs = &s->queue[queue_idx];
    int desc_idx;
    int read_size, write_size;
    uint16_t avail_idx;

    if (!qs->ready)
        return 0;
    avail_idx = virtio_read16(s, qs->avail_addr + 2);
    if (qs->last_avail_idx == avail_idx)
        return 0;
    desc_idx = virtio_read16(s, qs->avail_addr + 4 +
                             (qs->last_avail_idx & (qs->num - 1)) * 2);
    if (get_desc_rw_size(s, &read_size, &write_size, queue_idx, desc_idx))
        return 0;
    return write_size;
}

int virtio_console_write_data(VIRTIODevice *s, const uint8_t *buf, int buf_len)
{
    int queue_idx = 0;
    QueueState *qs = &s->queue[queue_idx];
    int desc_idx;
    uint16_t avail_idx;

    if (!qs->ready)
        return 0;
    avail_idx = virtio_read16(s, qs->avail_addr + 2);
    if (qs->last_avail_idx == avail_idx)
        return 0;
    desc_idx = virtio_read16(s, qs->avail_addr + 4 +
                             (qs->last_avail_idx & (qs->num - 1)) * 2);
    memcpy_to_queue(s, queue_idx, desc_idx, 0, buf, buf_len);
    virtio_consume_desc(s, queue_idx, desc_idx, buf_len);
    qs->last_avail_idx++;
    return buf_len;
}

/* send a resize event */
void virtio_console_resize_event(VIRTIODevice *s, int width, int height)
{
    /* indicate the console size */
    put_le16(s->config_space + 0, width);
    put_le16(s->config_space + 2, height);

    virtio_config_change_notify(s);
}

VIRTIODevice *virtio_console_init(VIRTIOBusDef *bus, CharacterDevice *cs)
{
    VIRTIOConsoleDevice *s = (VIRTIOConsoleDevice *)mallocz(sizeof(*s));

    virtio_init(&s->common, bus, 3, 4, virtio_console_recv_request);
    s->common.device_features = (1 << 0); /* VIRTIO_CONSOLE_F_SIZE */
    s->common.queue[0].manual_recv = TRUE;

    s->cs = cs;
    return (VIRTIODevice *)s;
}

/*********************************************************************/
/* input device */

enum {
    VIRTIO_INPUT_CFG_UNSET      = 0x00,
    VIRTIO_INPUT_CFG_ID_NAME    = 0x01,
    VIRTIO_INPUT_CFG_ID_SERIAL  = 0x02,
    VIRTIO_INPUT_CFG_ID_DEVIDS  = 0x03,
    VIRTIO_INPUT_CFG_PROP_BITS  = 0x10,
    VIRTIO_INPUT_CFG_EV_BITS    = 0x11,
    VIRTIO_INPUT_CFG_ABS_INFO   = 0x12,
};

#define VIRTIO_INPUT_EV_SYN 0x00
#define VIRTIO_INPUT_EV_KEY 0x01
#define VIRTIO_INPUT_EV_REL 0x02
#define VIRTIO_INPUT_EV_ABS 0x03
#define VIRTIO_INPUT_EV_REP 0x14

#define BTN_LEFT         0x110
#define BTN_RIGHT        0x111
#define BTN_MIDDLE       0x112
#define BTN_GEAR_DOWN    0x150
#define BTN_GEAR_UP      0x151

#define REL_X 0x00
#define REL_Y 0x01
#define REL_Z 0x02
#define REL_WHEEL 0x08

#define ABS_X 0x00
#define ABS_Y 0x01
#define ABS_Z 0x02

typedef struct VIRTIOInputDevice {
    VIRTIODevice common;
    VirtioInputTypeEnum type;
    uint32_t buttons_state;
} VIRTIOInputDevice;

static const uint16_t buttons_list[] = {
    BTN_LEFT, BTN_RIGHT, BTN_MIDDLE
};

static int virtio_input_recv_request(VIRTIODevice *s, int queue_idx,
                                      int desc_idx, int read_size,
                                      int write_size)
{
    if (queue_idx == 1) {
        /* led & keyboard updates */
        //        printf("%s: write_size=%d\n", __func__, write_size);
        virtio_consume_desc(s, queue_idx, desc_idx, 0);
    }
    return 0;
}

/* return < 0 if could not send key event */
static int virtio_input_queue_event(VIRTIODevice *s,
                                    uint16_t type, uint16_t code,
                                    uint32_t value)
{
    int queue_idx = 0;
    QueueState *qs = &s->queue[queue_idx];
    int desc_idx, buf_len;
    uint16_t avail_idx;
    uint8_t buf[8];

    if (!qs->ready)
        return -1;

    put_le16(buf, type);
    put_le16(buf + 2, code);
    put_le32(buf + 4, value);
    buf_len = 8;

    avail_idx = virtio_read16(s, qs->avail_addr + 2);
    if (qs->last_avail_idx == avail_idx)
        return -1;
    desc_idx = virtio_read16(s, qs->avail_addr + 4 +
                             (qs->last_avail_idx & (qs->num - 1)) * 2);
    //    printf("send: queue_idx=%d desc_idx=%d\n", queue_idx, desc_idx);
    memcpy_to_queue(s, queue_idx, desc_idx, 0, buf, buf_len);
    virtio_consume_desc(s, queue_idx, desc_idx, buf_len);
    qs->last_avail_idx++;
    return 0;
}

int virtio_input_send_key_event(VIRTIODevice *s, BOOL is_down,
                                uint16_t key_code)
{
    VIRTIOInputDevice *s1 = (VIRTIOInputDevice *)s;
    int ret;

    if (s1->type != VIRTIO_INPUT_TYPE_KEYBOARD)
        return -1;
    ret = virtio_input_queue_event(s, VIRTIO_INPUT_EV_KEY, key_code, is_down);
    if (ret)
        return ret;
    return virtio_input_queue_event(s, VIRTIO_INPUT_EV_SYN, 0, 0);
}

/* also used for the tablet */
int virtio_input_send_mouse_event(VIRTIODevice *s, int dx, int dy, int dz,
                                  unsigned int buttons)
{
    VIRTIOInputDevice *s1 = (VIRTIOInputDevice *)s;
    int ret, b, last_b;

    if (s1->type != VIRTIO_INPUT_TYPE_MOUSE &&
        s1->type != VIRTIO_INPUT_TYPE_TABLET)
        return -1;
    if (s1->type == VIRTIO_INPUT_TYPE_MOUSE) {
        ret = virtio_input_queue_event(s, VIRTIO_INPUT_EV_REL, REL_X, dx);
        if (ret != 0)
            return ret;
        ret = virtio_input_queue_event(s, VIRTIO_INPUT_EV_REL, REL_Y, dy);
        if (ret != 0)
            return ret;
    } else {
        ret = virtio_input_queue_event(s, VIRTIO_INPUT_EV_ABS, ABS_X, dx);
        if (ret != 0)
            return ret;
        ret = virtio_input_queue_event(s, VIRTIO_INPUT_EV_ABS, ABS_Y, dy);
        if (ret != 0)
            return ret;
    }
    if (dz != 0) {
        ret = virtio_input_queue_event(s, VIRTIO_INPUT_EV_REL, REL_WHEEL, dz);
        if (ret != 0)
            return ret;
    }

    if (buttons != s1->buttons_state) {
        for (unsigned int i = 0; i < countof(buttons_list); i++) {
            b = (buttons >> i) & 1;
            last_b = (s1->buttons_state >> i) & 1;
            if (b != last_b) {
                ret = virtio_input_queue_event(s, VIRTIO_INPUT_EV_KEY,
                                               buttons_list[i], b);
                if (ret != 0)
                    return ret;
            }
        }
        s1->buttons_state = buttons;
    }

    return virtio_input_queue_event(s, VIRTIO_INPUT_EV_SYN, 0, 0);
}

static void set_bit(uint8_t *tab, int k)
{
    tab[k >> 3] |= 1 << (k & 7);
}

static void virtio_input_config_write(VIRTIODevice *s)
{
    VIRTIOInputDevice *s1 = (VIRTIOInputDevice *)s;
    uint8_t *config = s->config_space;

    //    printf("config_write: %02x %02x\n", config[0], config[1]);
    switch (config[0]) {
    case VIRTIO_INPUT_CFG_UNSET:
        break;
    case VIRTIO_INPUT_CFG_ID_NAME:
        {
            const char *name;
            int len;
            switch (s1->type) {
            case VIRTIO_INPUT_TYPE_KEYBOARD:
                name = "virtio_keyboard";
                break;
            case VIRTIO_INPUT_TYPE_MOUSE:
                name = "virtio_mouse";
                break;
            case VIRTIO_INPUT_TYPE_TABLET:
                name = "virtio_tablet";
                break;
            default:
                abort();
            }
            len = strlen(name);
            config[2] = len;
            memcpy(config + 8, name, len);
        }
        break;
    default:
    case VIRTIO_INPUT_CFG_ID_SERIAL:
    case VIRTIO_INPUT_CFG_ID_DEVIDS:
    case VIRTIO_INPUT_CFG_PROP_BITS:
        config[2] = 0; /* size of reply */
        break;
    case VIRTIO_INPUT_CFG_EV_BITS:
        config[2] = 0;
        switch (s1->type) {
        case VIRTIO_INPUT_TYPE_KEYBOARD:
            switch (config[1]) {
            case VIRTIO_INPUT_EV_KEY:
                config[2] = 128 / 8;
                memset(config + 8, 0xff, 128 / 8); /* bitmap */
                break;
            case VIRTIO_INPUT_EV_REP: /* allow key repetition */
                config[2] = 1;
                break;
            default:
                break;
            }
            break;
        case VIRTIO_INPUT_TYPE_MOUSE:
            switch (config[1]) {
            case VIRTIO_INPUT_EV_KEY:
                config[2] = 512 / 8;
                memset(config + 8, 0, 512 / 8); /* bitmap */
                for (unsigned int i = 0; i < countof(buttons_list); i++)
                    set_bit(config + 8, buttons_list[i]);
                break;
            case VIRTIO_INPUT_EV_REL:
                config[2] = 2;
                config[8] = 0;
                config[9] = 0;
                set_bit(config + 8, REL_X);
                set_bit(config + 8, REL_Y);
                set_bit(config + 8, REL_WHEEL);
                break;
            default:
                break;
            }
            break;
        case VIRTIO_INPUT_TYPE_TABLET:
            switch (config[1]) {
            case VIRTIO_INPUT_EV_KEY:
                config[2] = 512 / 8;
                memset(config + 8, 0, 512 / 8); /* bitmap */
                for (unsigned int i = 0; i < countof(buttons_list); i++)
                    set_bit(config + 8, buttons_list[i]);
                break;
            case VIRTIO_INPUT_EV_REL:
                config[2] = 2;
                config[8] = 0;
                config[9] = 0;
                set_bit(config + 8, REL_WHEEL);
                break;
            case VIRTIO_INPUT_EV_ABS:
                config[2] = 1;
                config[8] = 0;
                set_bit(config + 8, ABS_X);
                set_bit(config + 8, ABS_Y);
                break;
            default:
                break;
            }
            break;
        default:
            abort();
        }
        break;
    case VIRTIO_INPUT_CFG_ABS_INFO:
        if (s1->type == VIRTIO_INPUT_TYPE_TABLET && config[1] <= 1) {
            /* for ABS_X and ABS_Y */
            config[2] = 5 * 4;
            put_le32(config + 8, 0); /* min */
            put_le32(config + 12, VIRTIO_INPUT_ABS_SCALE - 1) ; /* max */
            put_le32(config + 16, 0); /* fuzz */
            put_le32(config + 20, 0); /* flat */
            put_le32(config + 24, 0); /* res */
        }
        break;
    }
}

VIRTIODevice *virtio_input_init(VIRTIOBusDef *bus, VirtioInputTypeEnum type)
{
    VIRTIOInputDevice *s = (VIRTIOInputDevice *)mallocz(sizeof(*s));

    virtio_init(&s->common, bus, 18, 256, virtio_input_recv_request);
    s->common.queue[0].manual_recv = TRUE;
    s->common.device_features = 0;
    s->common.config_write = virtio_input_config_write;
    s->type = type;
    return (VIRTIODevice *)s;
}

/*********************************************************************/
/* 9p filesystem device */

typedef struct {
    struct list_head link;
    uint32_t fid;
    FSFile *fd;
} FIDDesc;

typedef struct VIRTIO9PDevice {
    VIRTIODevice common;
    FSDevice *fs;
    int msize; /* maximum message size */
    struct list_head fid_list; /* list of FIDDesc */
    BOOL req_in_progress;
} VIRTIO9PDevice;

static FIDDesc *fid_find1(VIRTIO9PDevice *s, uint32_t fid)
{
    struct list_head *el;
    FIDDesc *f;

    list_for_each(el, &s->fid_list) {
        f = list_entry(el, FIDDesc, link);
        if (f->fid == fid)
            return f;
    }
    return NULL;
}

static FSFile *fid_find(VIRTIO9PDevice *s, uint32_t fid)
{
    FIDDesc *f;

    f = fid_find1(s, fid);
    if (!f)
        return NULL;
    return f->fd;
}

static void fid_delete(VIRTIO9PDevice *s, uint32_t fid)
{
    FIDDesc *f;

    f = fid_find1(s, fid);
    if (f) {
        s->fs->fs_delete(s->fs, f->fd);
        list_del(&f->link);
        free(f);
    }
}

static void fid_set(VIRTIO9PDevice *s, uint32_t fid, FSFile *fd)
{
    FIDDesc *f = fid_find1(s, fid);
    if (f) {
        s->fs->fs_delete(s->fs, f->fd);
        f->fd = fd;
        return;
    }

    f = (FIDDesc *)malloc(sizeof(*f));
    f->fid = fid;
    f->fd = fd;
    list_add(&f->link, &s->fid_list);
}

#ifdef DEBUG_VIRTIO

typedef struct {
    uint8_t tag;
    const char *name;
} Virtio9POPName;

static const Virtio9POPName virtio_9p_op_names[] = {
    { 8, "statfs" },
    { 12, "lopen" },
    { 14, "lcreate" },
    { 16, "symlink" },
    { 18, "mknod" },
    { 22, "readlink" },
    { 24, "getattr" },
    { 26, "setattr" },
    { 30, "xattrwalk" },
    { 40, "readdir" },
    { 50, "fsync" },
    { 52, "lock" },
    { 54, "getlock" },
    { 70, "link" },
    { 72, "mkdir" },
    { 74, "renameat" },
    { 76, "unlinkat" },
    { 100, "version" },
    { 104, "attach" },
    { 108, "flush" },
    { 110, "walk" },
    { 116, "read" },
    { 118, "write" },
    { 120, "clunk" },
    { 0, NULL },
};

static const char *get_9p_op_name(int tag)
{
    const Virtio9POPName *p;
    for (p = virtio_9p_op_names; p->name != NULL; p++) {
        if (p->tag == tag)
            return p->name;
    }
    return NULL;
}

#endif /* DEBUG_VIRTIO */

static int marshall(VIRTIO9PDevice *s,
                    uint8_t *buf1, int max_len, const char *fmt, ...)
{
    va_list ap;
    int c;
    uint32_t val;
    uint64_t val64;
    uint8_t *buf, *buf_end;

#ifdef DEBUG_VIRTIO
    if (s->common.debug & VIRTIO_DEBUG_9P)
        printf(" ->");
#endif
    va_start(ap, fmt);
    buf = buf1;
    buf_end = buf1 + max_len;
    for (;;) {
        c = *fmt++;
        if (c == '\0')
            break;
        switch (c) {
        case 'b':
            assert(buf + 1 <= buf_end);
            val = va_arg(ap, int);
#ifdef DEBUG_VIRTIO
            if (s->common.debug & VIRTIO_DEBUG_9P)
                printf(" b=%d", val);
#endif
            buf[0] = val;
            buf += 1;
            break;
        case 'h':
            assert(buf + 2 <= buf_end);
            val = va_arg(ap, int);
#ifdef DEBUG_VIRTIO
            if (s->common.debug & VIRTIO_DEBUG_9P)
                printf(" h=%d", val);
#endif
            put_le16(buf, val);
            buf += 2;
            break;
        case 'w':
            assert(buf + 4 <= buf_end);
            val = va_arg(ap, int);
#ifdef DEBUG_VIRTIO
            if (s->common.debug & VIRTIO_DEBUG_9P)
                printf(" w=%d", val);
#endif
            put_le32(buf, val);
            buf += 4;
            break;
        case 'd':
            assert(buf + 8 <= buf_end);
            val64 = va_arg(ap, uint64_t);
#ifdef DEBUG_VIRTIO
            if (s->common.debug & VIRTIO_DEBUG_9P)
                printf(" d=%" PRId64, val64);
#endif
            put_le64(buf, val64);
            buf += 8;
            break;
        case 's':
            {
                char *str;
                int len;
                str = va_arg(ap, char *);
#ifdef DEBUG_VIRTIO
                if (s->common.debug & VIRTIO_DEBUG_9P)
                    printf(" s=\"%s\"", str);
#endif
                len = strlen(str);
                assert(len <= 65535);
                assert(buf + 2 + len <= buf_end);
                put_le16(buf, len);
                buf += 2;
                memcpy(buf, str, len);
                buf += len;
            }
            break;
        case 'Q':
            {
                FSQID *qid;
                assert(buf + 13 <= buf_end);
                qid = va_arg(ap, FSQID *);
#ifdef DEBUG_VIRTIO
                if (s->common.debug & VIRTIO_DEBUG_9P)
                    printf(" Q=%d:%d:%" PRIu64, qid->type, qid->version, qid->path);
#endif
                buf[0] = qid->type;
                put_le32(buf + 1, qid->version);
                put_le64(buf + 5, qid->path);
                buf += 13;
            }
            break;
        default:
            abort();
        }
    }
    va_end(ap);
    return buf - buf1;
}

/* return < 0 if error */
/* XXX: free allocated strings in case of error */
static int unmarshall(VIRTIO9PDevice *s, int queue_idx,
                      int desc_idx, int *poffset, const char *fmt, ...)
{
    VIRTIODevice *s1 = (VIRTIODevice *)s;
    va_list ap;
    int offset, c;
    uint8_t buf[16];

    offset = *poffset;
    va_start(ap, fmt);
    for (;;) {
        c = *fmt++;
        if (c == '\0')
            break;
        switch (c) {
        case 'b':
            {
                uint8_t *ptr;
                if (memcpy_from_queue(s1, buf, queue_idx, desc_idx, offset, 1))
                    return -1;
                ptr = va_arg(ap, uint8_t *);
                *ptr = buf[0];
                offset += 1;
#ifdef DEBUG_VIRTIO
                if (s->common.debug & VIRTIO_DEBUG_9P)
                    printf(" b=%d", *ptr);
#endif
            }
            break;
        case 'h':
            {
                uint16_t *ptr;
                if (memcpy_from_queue(s1, buf, queue_idx, desc_idx, offset, 2))
                    return -1;
                ptr = va_arg(ap, uint16_t *);
                *ptr = get_le16(buf);
                offset += 2;
#ifdef DEBUG_VIRTIO
                if (s->common.debug & VIRTIO_DEBUG_9P)
                    printf(" h=%d", *ptr);
#endif
            }
            break;
        case 'w':
            {
                uint32_t *ptr;
                if (memcpy_from_queue(s1, buf, queue_idx, desc_idx, offset, 4))
                    return -1;
                ptr = va_arg(ap, uint32_t *);
                *ptr = get_le32(buf);
                offset += 4;
#ifdef DEBUG_VIRTIO
                if (s->common.debug & VIRTIO_DEBUG_9P)
                    printf(" w=%d", *ptr);
#endif
            }
            break;
        case 'd':
            {
                uint64_t *ptr;
                if (memcpy_from_queue(s1, buf, queue_idx, desc_idx, offset, 8))
                    return -1;
                ptr = va_arg(ap, uint64_t *);
                *ptr = get_le64(buf);
                offset += 8;
#ifdef DEBUG_VIRTIO
                if (s->common.debug & VIRTIO_DEBUG_9P)
                    printf(" d=%" PRId64, *ptr);
#endif
            }
            break;
        case 's':
            {
                int len;

                if (memcpy_from_queue(s1, buf, queue_idx, desc_idx, offset, 2))
                    return -1;
                len = get_le16(buf);
                offset += 2;

                char *str = (char *)malloc(len + 1);
                if (memcpy_from_queue(s1, str, queue_idx, desc_idx, offset, len))
                    return -1;
                str[len] = '\0';
                offset += len;

                char **ptr = va_arg(ap, char **);
                *ptr = str;
#ifdef DEBUG_VIRTIO
                if (s->common.debug & VIRTIO_DEBUG_9P)
                    printf(" s=\"%s\"", *ptr);
#endif
            }
            break;
        default:
            abort();
        }
    }
    va_end(ap);
    *poffset = offset;
    return 0;
}

static void virtio_9p_send_reply(VIRTIO9PDevice *s, int queue_idx,
                                 int desc_idx, uint8_t id, uint16_t tag,
                                 uint8_t *buf, int buf_len)
{
    int len;

#ifdef DEBUG_VIRTIO
    if (s->common.debug & VIRTIO_DEBUG_9P) {
        if (id == 6)
            printf(" (error)");
        printf("\n");
    }
#endif
    len = buf_len + 7;
    uint8_t *buf1 = (uint8_t *)malloc(len);
    put_le32(buf1, len);
    buf1[4] = id + 1;
    put_le16(buf1 + 5, tag);
    memcpy(buf1 + 7, buf, buf_len);
    memcpy_to_queue((VIRTIODevice *)s, queue_idx, desc_idx, 0, buf1, len);
    virtio_consume_desc((VIRTIODevice *)s, queue_idx, desc_idx, len);
    free(buf1);
}

static void virtio_9p_send_error(VIRTIO9PDevice *s, int queue_idx,
                                 int desc_idx, uint16_t tag, uint32_t error)
{
    uint8_t buf[4];
    int buf_len;

    buf_len = marshall(s, buf, sizeof(buf), "w", -error);
    virtio_9p_send_reply(s, queue_idx, desc_idx, 6, tag, buf, buf_len);
}

typedef struct {
    VIRTIO9PDevice *dev;
    int queue_idx;
    int desc_idx;
    uint16_t tag;
} P9OpenInfo;

static void virtio_9p_open_reply(FSDevice *fs, FSQID *qid, int err,
                                 P9OpenInfo *oi)
{
    VIRTIO9PDevice *s = oi->dev;
    uint8_t buf[32];
    int buf_len;

    if (err < 0) {
        virtio_9p_send_error(s, oi->queue_idx, oi->desc_idx, oi->tag, err);
    } else {
        buf_len = marshall(s, buf, sizeof(buf),
                           "Qw", qid, s->msize - 24);
        virtio_9p_send_reply(s, oi->queue_idx, oi->desc_idx, 12, oi->tag,
                             buf, buf_len);
    }
    free(oi);
}

static void virtio_9p_open_cb(FSDevice *fs, FSQID *qid, int err,
                              void *opaque)
{
    P9OpenInfo *oi = (P9OpenInfo *)opaque;
    VIRTIO9PDevice *s = oi->dev;
    int queue_idx = oi->queue_idx;

    virtio_9p_open_reply(fs, qid, err, oi);

    s->req_in_progress = FALSE;

    /* handle next requests */
    queue_notify((VIRTIODevice *)s, queue_idx);
}

static int virtio_9p_recv_request(VIRTIODevice *s1, int queue_idx,
                                   int desc_idx, int read_size,
                                   int write_size)
{
    VIRTIO9PDevice *s = (VIRTIO9PDevice *)s1;
    int offset, header_len;
    uint8_t id;
    uint16_t tag;
    uint8_t buf[1024];
    int buf_len, err;
    FSDevice *fs = s->fs;

    if (queue_idx != 0)
        return 0;

    if (s->req_in_progress)
        return -1;

    offset = 0;
    header_len = 4 + 1 + 2;
    if (memcpy_from_queue(s1, buf, queue_idx, desc_idx, offset, header_len)) {
        tag = 0;
        goto protocol_error;
    }
    //size = get_le32(buf);
    id = buf[4];
    tag = get_le16(buf + 5);
    offset += header_len;

#ifdef DEBUG_VIRTIO
    if (s1->debug & VIRTIO_DEBUG_9P) {
        const char *name;
        name = get_9p_op_name(id);
        printf("9p: op=");
        if (name)
            printf("%s", name);
        else
            printf("%d", id);
    }
#endif
    /* Note: same subset as JOR1K */
    switch (id) {
    case 8: /* statfs */
        {
            FSStatFS st;

            fs->fs_statfs(fs, &st);
            buf_len = marshall(s, buf, sizeof(buf),
                               "wwddddddw",
                               0,
                               st.f_bsize,
                               st.f_blocks,
                               st.f_bfree,
                               st.f_bavail,
                               st.f_files,
                               st.f_ffree,
                               0, /* id */
                               256 /* max filename length */
                               );
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 12: /* lopen */
        {
            uint32_t fid, flags;
            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "ww", &fid, &flags))
                goto protocol_error;

            FSFile *f = fid_find(s, fid);
            if (!f)
                goto fid_not_found;

            P9OpenInfo *oi = (P9OpenInfo *)malloc(sizeof(*oi));
            oi->dev = s;
            oi->queue_idx = queue_idx;
            oi->desc_idx = desc_idx;
            oi->tag = tag;

            FSQID qid;
            err = fs->fs_open(fs, &qid, f, flags, virtio_9p_open_cb, oi);
            if (err <= 0) {
                virtio_9p_open_reply(fs, &qid, err, oi);
            } else {
                s->req_in_progress = TRUE;
            }
        }
        break;
    case 14: /* lcreate */
        {
            uint32_t fid, flags, mode, gid;
            char *name;
            FSFile *f;
            FSQID qid;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wswww", &fid, &name, &flags, &mode, &gid))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f) {
                err = -P9_EPROTO;
            } else {
                err = fs->fs_create(fs, &qid, f, name, flags, mode, gid);
            }
            free(name);
            if (err)
                goto error;
            buf_len = marshall(s, buf, sizeof(buf),
                               "Qw", &qid, s->msize - 24);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 16: /* symlink */
        {
            uint32_t fid, gid;
            char *name, *symgt;
            FSFile *f;
            FSQID qid;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wssw", &fid, &name, &symgt, &gid))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f) {
                err = -P9_EPROTO;
            } else {
                err = fs->fs_symlink(fs, &qid, f, name, symgt, gid);
            }
            free(name);
            free(symgt);
            if (err)
                goto error;
            buf_len = marshall(s, buf, sizeof(buf),
                               "Q", &qid);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 18: /* mknod */
        {
            uint32_t fid, mode, major, minor, gid;
            char *name;
            FSFile *f;
            FSQID qid;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wswwww", &fid, &name, &mode, &major, &minor, &gid))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f) {
                err = -P9_EPROTO;
            } else {
                err = fs->fs_mknod(fs, &qid, f, name, mode, major, minor, gid);
            }
            free(name);
            if (err)
                goto error;
            buf_len = marshall(s, buf, sizeof(buf),
                               "Q", &qid);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 22: /* readlink */
        {
            uint32_t fid;
            char buf1[1024];
            FSFile *f;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "w", &fid))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f) {
                err = -P9_EPROTO;
            } else {
                err = fs->fs_readlink(fs, buf1, sizeof(buf1), f);
            }
            if (err)
                goto error;
            buf_len = marshall(s, buf, sizeof(buf), "s", buf1);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 24: /* getattr */
        {
            uint32_t fid;
            uint64_t mask;
            FSFile *f;
            FSStat st;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wd", &fid, &mask))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                goto fid_not_found;
            err = fs->fs_stat(fs, f, &st);
            if (err)
                goto error;

            buf_len = marshall(s, buf, sizeof(buf),
                               "dQwwwddddddddddddddd",
                               mask, &st.qid,
                               st.st_mode, st.st_uid, st.st_gid,
                               st.st_nlink, st.st_rdev, st.st_size,
                               st.st_blksize, st.st_blocks,
                               st.st_atime_sec, (uint64_t)st.st_atime_nsec,
                               st.st_mtime_sec, (uint64_t)st.st_mtime_nsec,
                               st.st_ctime_sec, (uint64_t)st.st_ctime_nsec,
                               (uint64_t)0, (uint64_t)0,
                               (uint64_t)0, (uint64_t)0);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 26: /* setattr */
        {
            uint32_t fid, mask, mode, uid, gid;
            uint64_t size, atime_sec, atime_nsec, mtime_sec, mtime_nsec;
            FSFile *f;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wwwwwddddd", &fid, &mask, &mode, &uid, &gid,
                           &size, &atime_sec, &atime_nsec,
                           &mtime_sec, &mtime_nsec))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                goto fid_not_found;
            err = fs->fs_setattr(fs, f, mask, mode, uid, gid, size, atime_sec,
                                 atime_nsec, mtime_sec, mtime_nsec);
            if (err)
                goto error;
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, NULL, 0);
        }
        break;
    case 30: /* xattrwalk */
        {
            /* not supported yet */
            err = -P9_ENOTSUP;
            goto error;
        }
        break;
    case 40: /* readdir */
        {
            uint32_t fid, count;
            uint64_t offs;
            uint8_t *buf;
            int n;
            FSFile *f;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wdw", &fid, &offs, &count))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                goto fid_not_found;
            buf = (uint8_t *)malloc(count + 4);
            n = fs->fs_readdir(fs, f, offs, buf + 4, count);
            if (n < 0) {
                err = n;
                goto error;
            }
            put_le32(buf, n);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, n + 4);
            free(buf);
        }
        break;
    case 50: /* fsync */
        {
            uint32_t fid;
            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "w", &fid))
                goto protocol_error;
            /* ignored */
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, NULL, 0);
        }
        break;
    case 52: /* lock */
        {
            uint32_t fid;
            FSFile *f;
            FSLock lock;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wbwddws", &fid, &lock.type, &lock.flags,
                           &lock.start, &lock.length,
                           &lock.proc_id, &lock.client_id))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                err = -P9_EPROTO;
            else
                err = fs->fs_lock(fs, f, &lock);
            free(lock.client_id);
            if (err < 0)
                goto error;
            buf_len = marshall(s, buf, sizeof(buf), "b", err);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 54: /* getlock */
        {
            uint32_t fid;
            FSFile *f;
            FSLock lock;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wbddws", &fid, &lock.type,
                           &lock.start, &lock.length,
                           &lock.proc_id, &lock.client_id))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                err = -P9_EPROTO;
            else
                err = fs->fs_getlock(fs, f, &lock);
            if (err < 0) {
                free(lock.client_id);
                goto error;
            }
            buf_len = marshall(s, buf, sizeof(buf), "bddws",
                               &lock.type,
                               &lock.start, &lock.length,
                               &lock.proc_id, &lock.client_id);
            free(lock.client_id);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 70: /* link */
        {
            uint32_t dfid, fid;
            char *name;
            FSFile *f, *df;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wws", &dfid, &fid, &name))
                goto protocol_error;
            df = fid_find(s, dfid);
            f = fid_find(s, fid);
            if (!df || !f) {
                err = -P9_EPROTO;
            } else {
                err = fs->fs_link(fs, df, f, name);
            }
            free(name);
            if (err)
                goto error;
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, NULL, 0);
        }
        break;
    case 72: /* mkdir */
        {
            uint32_t fid, mode, gid;
            char *name;
            FSFile *f;
            FSQID qid;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wsww", &fid, &name, &mode, &gid))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                goto fid_not_found;
            err = fs->fs_mkdir(fs, &qid, f, name, mode, gid);
            if (err != 0)
                goto error;
            buf_len = marshall(s, buf, sizeof(buf), "Q", &qid);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 74: /* renameat */
        {
            uint32_t fid, new_fid;
            char *name, *new_name;
            FSFile *f, *new_f;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wsws", &fid, &name, &new_fid, &new_name))
                goto protocol_error;
            f = fid_find(s, fid);
            new_f = fid_find(s, new_fid);
            if (!f || !new_f) {
                err = -P9_EPROTO;
            } else {
                err = fs->fs_renameat(fs, f, name, new_f, new_name);
            }
            free(name);
            free(new_name);
            if (err != 0)
                goto error;
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, NULL, 0);
        }
        break;
    case 76: /* unlinkat */
        {
            uint32_t fid, flags;
            char *name;
            FSFile *f;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wsw", &fid, &name, &flags))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f) {
                err = -P9_EPROTO;
            } else {
                err = fs->fs_unlinkat(fs, f, name);
            }
            free(name);
            if (err != 0)
                goto error;
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, NULL, 0);
        }
        break;
    case 100: /* version */
        {
            uint32_t msize;
            char *version;
            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "ws", &msize, &version))
                goto protocol_error;
            s->msize = msize;
            //            printf("version: msize=%d version=%s\n", msize, version);
            free(version);
            buf_len = marshall(s, buf, sizeof(buf), "ws", s->msize, "9P2000.L");
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 104: /* attach */
        {
            uint32_t fid, afid, uid;
            char *uname, *aname;
            FSQID qid;
            FSFile *f;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wwssw", &fid, &afid, &uname, &aname, &uid))
                goto protocol_error;
            err = fs->fs_attach(fs, &f, &qid, uid, uname, aname);
            if (err != 0)
                goto error;
            fid_set(s, fid, f);
            free(uname);
            free(aname);
            buf_len = marshall(s, buf, sizeof(buf), "Q", &qid);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 108: /* flush */
        {
            uint16_t oldtag;
            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "h", &oldtag))
                goto protocol_error;
            /* ignored */
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, NULL, 0);
        }
        break;
    case 110: /* walk */
        {
            uint32_t fid, newfid;
            uint16_t nwname;
            FSQID *qids;
            char **names;
            FSFile *f;
            int i;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wwh", &fid, &newfid, &nwname))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                goto fid_not_found;
            names = (char **)mallocz(sizeof(names[0]) * nwname);
            qids = (FSQID *)malloc(sizeof(qids[0]) * nwname);
            for (i = 0; i < nwname; i++) {
                if (unmarshall(s, queue_idx, desc_idx, &offset,
                               "s", &names[i])) {
                    err = -P9_EPROTO;
                    goto walk_done;
                }
            }
            err = fs->fs_walk(fs, &f, qids, f, nwname, names);
        walk_done:
            for (i = 0; i < nwname; i++) {
                free(names[i]);
            }
            free(names);
            if (err < 0) {
                free(qids);
                goto error;
            }
            buf_len = marshall(s, buf, sizeof(buf), "h", err);
            for (i = 0; i < err; i++) {
                buf_len += marshall(s, buf + buf_len, sizeof(buf) - buf_len,
                                    "Q", &qids[i]);
            }
            free(qids);
            fid_set(s, newfid, f);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 116: /* read */
        {
            uint32_t fid, count;
            uint64_t offs;
            uint8_t *buf;
            int n;
            FSFile *f;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wdw", &fid, &offs, &count))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                goto fid_not_found;
            buf = (uint8_t *)malloc(count + 4);
            n = fs->fs_read(fs, f, offs, buf + 4, count);
            if (n < 0) {
                err = n;
                free(buf);
                goto error;
            }
            put_le32(buf, n);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, n + 4);
            free(buf);
        }
        break;
    case 118: /* write */
        {
            uint32_t fid, count;
            uint64_t offs;
            uint8_t *buf1;
            int n;
            FSFile *f;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "wdw", &fid, &offs, &count))
                goto protocol_error;
            f = fid_find(s, fid);
            if (!f)
                goto fid_not_found;
            buf1 = (uint8_t *)malloc(count);
            if (memcpy_from_queue(s1, buf1, queue_idx, desc_idx, offset,
                                  count)) {
                free(buf1);
                goto protocol_error;
            }
            n = fs->fs_write(fs, f, offs, buf1, count);
            free(buf1);
            if (n < 0) {
                err = n;
                goto error;
            }
            buf_len = marshall(s, buf, sizeof(buf), "w", n);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, buf, buf_len);
        }
        break;
    case 120: /* clunk */
        {
            uint32_t fid;

            if (unmarshall(s, queue_idx, desc_idx, &offset,
                           "w", &fid))
                goto protocol_error;
            fid_delete(s, fid);
            virtio_9p_send_reply(s, queue_idx, desc_idx, id, tag, NULL, 0);
        }
        break;
    default:
        printf("9p: unsupported operation id=%d\n", id);
        goto protocol_error;
    }
    return 0;
 error:
    virtio_9p_send_error(s, queue_idx, desc_idx, tag, err);
    return 0;
 protocol_error:
 fid_not_found:
    err = -P9_EPROTO;
    goto error;
}

VIRTIODevice *virtio_9p_init(VIRTIOBusDef *bus, FSDevice *fs,
                             const char *mount_tag)

{
    int len = strlen(mount_tag);
    VIRTIO9PDevice *s = (VIRTIO9PDevice *)mallocz(sizeof(*s));
    virtio_init(&s->common, bus,
                9, 2 + len, virtio_9p_recv_request);
    s->common.device_features = 1 << 0;

    /* set the mount tag */
    uint8_t *cfg = s->common.config_space;
    cfg[0] = len;
    cfg[1] = len >> 8;
    memcpy(cfg + 2, mount_tag, len);

    s->fs = fs;
    s->msize = 8192;
    init_list_head(&s->fid_list);

    return (VIRTIODevice *)s;
}
