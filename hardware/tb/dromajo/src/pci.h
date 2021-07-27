/*
 * Simple PCI bus driver
 *
 * Copyright (c) 2017 Fabrice Bellard
 * Copyright (C) 2017,2018,2019, Esperanto Technologies Inc.
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
#ifndef PCI_H
#define PCI_H

#include "iomem.h"

typedef struct PCIBus PCIBus;
typedef struct PCIDevice PCIDevice;

/* bar type */
#define PCI_ADDRESS_SPACE_MEM		0x00
#define PCI_ADDRESS_SPACE_IO		0x01
#define PCI_ADDRESS_SPACE_MEM_PREFETCH	0x08

#define PCI_ROM_SLOT 6
#define PCI_NUM_REGIONS 7

/* PCI config addresses */
#define PCI_VENDOR_ID		0x00	/* 16 bits */
#define PCI_DEVICE_ID		0x02	/* 16 bits */
#define PCI_COMMAND		0x04	/* 16 bits */
#define PCI_COMMAND_IO		(1 << 0)
#define PCI_COMMAND_MEMORY	(1 << 1)
#define PCI_STATUS		0x06	/* 16 bits */
#define  PCI_STATUS_CAP_LIST	(1 << 4)
#define PCI_CLASS_PROG		0x09
#define PCI_SUBSYSTEM_VENDOR_ID	0x2c    /* 16 bits */
#define PCI_SUBSYSTEM_ID	0x2e    /* 16 bits */
#define PCI_CAPABILITY_LIST	0x34    /* 8 bits */
#define PCI_INTERRUPT_LINE	0x3c    /* 8 bits */
#define PCI_INTERRUPT_PIN	0x3d    /* 8 bits */

typedef void PCIBarSetFunc(void *opaque, int bar_num, uint32_t addr,
                           BOOL enabled);

PCIDevice *pci_register_device(PCIBus *b, const char *name, int devfn,
                               uint16_t vendor_id, uint16_t device_id,
                               uint8_t revision, uint16_t class_id);
PhysMemoryMap *pci_device_get_mem_map(PCIDevice *d);
PhysMemoryMap *pci_device_get_port_map(PCIDevice *d);
void pci_register_bar(PCIDevice *d, unsigned int bar_num,
                      uint32_t size, int type,
                      void *opaque, PCIBarSetFunc *bar_set);
IRQSignal *pci_device_get_irq(PCIDevice *d, unsigned int irq_num);
uint8_t *pci_device_get_dma_ptr(PCIDevice *d, uint64_t addr);
void pci_device_set_config8(PCIDevice *d, uint8_t addr, uint8_t val);
void pci_device_set_config16(PCIDevice *d, uint8_t addr, uint16_t val);
int pci_device_get_devfn(PCIDevice *d);
int pci_add_capability(PCIDevice *d, const uint8_t *buf, int size);

typedef struct I440FXState I440FXState;

I440FXState *i440fx_init(PCIBus **pbus, int *ppiix3_devfn,
                         PhysMemoryMap *mem_map, PhysMemoryMap *port_map,
                         IRQSignal *pic_irqs);
void i440fx_map_interrupts(I440FXState *s, uint8_t *elcr,
                           const uint8_t *pci_irqs);

#endif /* PCI_H */
