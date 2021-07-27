/*
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
 */
#include <stdint.h>
#include "virtio.h"

typedef struct DW_apb_uart_state {
    CharacterDevice       *cs;
    uint32_t               irq;
    uint8_t                rx_fifo[8];
    unsigned int           rx_fifo_len;

    uint16_t               div_latch;    // divisor latch         (0x00/0x04)
    uint8_t		   rbr;          // receive buffer register    (0x00)
    uint8_t  		   ier;          // interrupt enable register  (0x04)
    uint8_t                fcr;          // FIFO control register      (0x08)
    uint8_t  		   iid;          // interrupt identity register(0x08)
    uint8_t  		   lcr;          // line control register      (0x0c)
    uint8_t  		   lsr;          // line status register       (0x14)

} DW_apb_uart_state;

// Fake Synopsys™ DesignWare™ ABP™ UART (the ET UART)
#define DW_APB_UART0_BASE_ADDR      0x12002000
#define DW_APB_UART0_SIZE               0x1000
#define DW_APB_UART0_IRQ                     3 // XXX It's ID 3 which I presume is the PLIC source input
#define DW_APB_UART0_FREQ             25000000 // 25 MHz
#define DW_APB_UART1_BASE_ADDR      0x12007000
#define DW_APB_UART1_IRQ                    15 // XXX It's ID 15 which I presume is the PLIC source input

uint32_t dw_apb_uart_read (void *opaque, uint32_t offset,               int size_log2);
void     dw_apb_uart_write(void *opaque, uint32_t offset, uint32_t val, int size_log2);
