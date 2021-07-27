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
#include "dw_apb_uart.h"
#include <stdio.h>
#include <assert.h>

static const char *reg_names[256/4] = {
    "rx buf / div latch lo",
    "intr en / div latch hi",
    "intr id / FIFO ctrl",
    "line control",
    "modem control",
    "line status",
    "modem status",
    "scratch",
    "reserved0",
    "reserved1",
    "reserved2",
    "reserved3",
    "shadow rx/tx buf0",
    "shadow rx/tx buf1",
    "shadow rx/tx buf2",
    "shadow rx/tx buf3",
    "shadow rx/tx buf4",
    "shadow rx/tx buf5",
    "shadow rx/tx buf6",
    "shadow rx/tx buf7",
    "shadow rx/tx buf8",
    "shadow rx/tx buf9",
    "shadow rx/tx buf10",
    "shadow rx/tx buf11",
    "shadow rx/tx buf12",
    "shadow rx/tx buf13",
    "shadow rx/tx buf14",
    "shadow rx/tx buf15",
    "FIFO access",
    "tx FIFO read",
    "rxr FIFO write",
    "uart status",
    "tx FIFO level",
    "rx FIFO level",
    "software reset",
    "shadow RTS",
    "shadow break control",
    "shadow dma mode",
    "shadow FIFO enable",
    "shadow rx trigger",
    "shadow tx trigger",
    "halt Tx",
    "dma software ack",

#ifndef __cplusplus
    [0xf4/4] = "component parameters",
    [0xf8/4] = "component version",
    [0xfc/4] = "component type",
#endif
};

/* The most important registers (only ones implemented) */

enum {
    uart_reg_rx_buf     = 0x00,
    uart_reg_intren     = 0x04,
    uart_reg_intrid     = 0x08,
    uart_reg_linecontrol= 0x0c,

    uart_reg_linestatus = 0x14,
    uart_reg_comptype   = 0xfc,
};

/* Configuration parameters at hardware instantiation time (only includes features relevant to sim) */
#define FEATURE_FIFO_MODE              64
#define FEATURE_REG_TIMEOUT_WIDTH       4
#define FEATURE_HC_REG_TIMEOUT_VALUE    0
#define FEATURE_REG_TIMEOUT_VALUE       8
#define FEATURE_UART_RS485_INTERFACE_EN 0
#define FEATURE_UART_9BIT_DATA_EN       0
#define FEATURE_APB_DATA_WIDTH         32
#define FEATURE_MEM_SELECT_USER         1  // == internal
#define FEATURE_SIR_MODE                0 // disabled
#define FEATURE_AFCE_MODE               0
#define FEATURE_THRE_MODE_USER          1 // enabled
#define FEATURE_FIFO_ACCESS             1 // programmable FIFOQ access mode enabled
#define FEATURE_ADDITIONAL_FEATURES     1
#define FEATURE_FIFO_STAT               1
#define FEATURE_SHADOW                  1
#define FEATURE_UART_ADD_ENCODED_PARAMS 1
#define FEATURE_UART_16550_COMPATIBLE   0
#define FEATURE_FRACTIONAL_BAUD_DIVISOR_EN 1
#define FEATURE_DLF_SIZE                4
#define FEATURE_LSR_STATUS_CLEAR        0 // Both RBR Read and LSR Read clears OE, PE, FE, and BI

//#define DEBUG(fmt ...) fprintf(dromajo_stderr, fmt)
#define DEBUG(fmt ...) (void) 0

uint32_t dw_apb_uart_read(void *opaque, uint32_t offset, int size_log2)
{
    DW_apb_uart_state *s = (DW_apb_uart_state *)opaque;
    int res = 0;

    assert(offset % 4 == 0 && offset/4 < 64);

    switch (offset) {
    case uart_reg_rx_buf: // 0x00
        if (s->lcr & (1 << 7)) {
            res = s->div_latch & 255;
        } else {
            res = s->rbr;
            s->lsr &= ~1;

            // XXX more side effects here, opt. drain FIFO when in FIFO mode
            // Read from device maybe

            if (FEATURE_LSR_STATUS_CLEAR == 0)
                s->lsr &= ~30; // Reading clears BI, FE, PE, OE
        }
        break;

    case uart_reg_intren: // 0x04
        if (s->lcr & (1 << 7)) {
            res = s->div_latch >> 8;
        } else {
            res = s->ier;
        }
        break;


    case uart_reg_intrid: // 0x08
        s->iid = 1; // XXX Value After Reset
        res = ((s->fcr & 1) ? 0xc0 : 0) + s->iid;
        break;

    case uart_reg_linecontrol: // 0x0c
        res = s->lcr;
        break;

    case uart_reg_linestatus: // 0x14
        res = s->lsr;
        s->lsr |= (1 << 6) | (1 << 5); // TX empty, Holding Empty
        s->lsr &= ~30; // Reading clears BI, FE, PE, OE

        if (!(s->lsr & 1)) {
            CharacterDevice *cs = s->cs;
            uint8_t buf;

            if (cs->read_data(cs->opaque, &buf, 1)) {
                s->lsr |= 1;
                s->rbr = buf;
            }
        }
        break;

    case uart_reg_comptype: // 0xfc
    default:;
    }

    if (reg_names[offset/4])
        DEBUG("dw_apb_uart_read(0x%02x \"%s\") -> %d\n", offset, reg_names[offset/4], res);
    else
        DEBUG("dw_apb_uart_read(0x%02x, %d) -> %d\n", offset, size_log2, res);

    return res;
}

void dw_apb_uart_write(void *opaque, uint32_t offset, uint32_t val, int size_log2)
{
    DW_apb_uart_state *s = (DW_apb_uart_state *)opaque;

    val &= 255;

    assert(offset % 4 == 0 && offset/4 < 64);

    if (reg_names[offset/4] && size_log2 == 2)
        DEBUG("dw_apb_uart_write(0x%02x \"%s\", %d)\n", offset, reg_names[offset/4], val);
    else
        DEBUG("dw_apb_uart_write(0x%02x, %d, %d)\n", offset, val, size_log2);

    switch (offset) {
    case uart_reg_rx_buf: // 0x00
        if (s->lcr & (1 << 7)) {
            s->div_latch = (s->div_latch & ~255) + val;
            DEBUG("     div latch is now %d\n", s->div_latch);
        } else {
            CharacterDevice *cs = s->cs;
            unsigned char ch = val;
            DEBUG("   TRANSMIT '%c' (0x%02x)\n", val, val);
            cs->write_data(cs->opaque, &ch, 1);
            s->lsr &= ~(1 << 5); // XXX Assumes non-fifo mode
            s->lsr &= ~(1 << 6);
        }
        break;

    case uart_reg_intren: // 0x04
        if (s->lcr & (1 << 7)) {
            s->div_latch = (s->div_latch & 255) + val * 256;
            DEBUG("     div latch is now %d\n", s->div_latch);
        } else {
            s->ier = val & (FEATURE_THRE_MODE_USER ? 0xFF : 0x7F);
        }
        break;

    case uart_reg_intrid: // 0x08
        s->fcr = val;
        for (int i = 0; i < 8; ++i)
            if (s->fcr & (1 << i))
                switch (i) {
                case 0:
                    DEBUG("    FIFO enable\n");
                    break;
                case 1:
                    DEBUG("    receiver FIFO reset\n");
                    break;
                case 2:
                    DEBUG("    transmitter FIFO reset\n");
                    break;
                case 3:
                    DEBUG("    dma mode\n");
                    break;
                case 4:
                    DEBUG("    transmitter empty trigger\n");
                    break;
                case 6:
                    DEBUG("    receiver trigger\n");
                    break;
                default:
                    DEBUG("    ?? bit %d isn't implemented\n", i);
                    break;
                }
        break;

    case uart_reg_linecontrol: // 0x0c
        s->lcr = val;
        DEBUG("    %d bits per character\n", (val & 3) + 5);
        break;

    default:;
        DEBUG("    ignored write\n");
        break;
    }
}
