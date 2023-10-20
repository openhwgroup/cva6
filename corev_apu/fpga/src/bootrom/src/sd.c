// Copyright OpenHW Group contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sd.h"
#include "spi.h"
#include "uart.h"

// spi full duplex: send 0xff to receive byte
uint8_t sd_dummy()
{
    return spi_txrx(0xFF);
}

uint8_t sd_cmd(uint8_t cmd, uint32_t arg, uint8_t crc)
{
    unsigned long n;
    uint8_t r;

    sd_dummy();
    spi_txrx(0x40 | cmd);
    spi_txrx(arg >> 24);
    spi_txrx(arg >> 16);
    spi_txrx(arg >> 8);
    spi_txrx(arg);
    spi_txrx(crc);

    n = 100;
    do
    {
        r = sd_dummy();
        if (!(r & 0x80))
        {
            break;
        }
    } while (--n > 0);
    if (n == 0)
    {
        // print_uart("could not find valid sd response\r\n");
    }
    return r;
}

void print_status(const char *cmd, uint8_t response)
{
    print_uart("SD command ");
    print_uart(cmd);
    print_uart(" \tresponse : ");
    print_uart_byte(response);
    print_uart("\r\n");
}

int sd_cmd0()
{
    int counter = 10000;
    uint8_t r = 0xff;
    while (r != 0x1)
    {
        r = sd_cmd(0, 0, 0x95);
        sd_dummy(); // R1: 1 Byte response
        counter--;
        if (counter <= 0)
            return 1 == 0;
    }
    print_status("cmd0", r);
    return r == 0x1;
}

int sd_cmd8()
{
    uint8_t r1 = sd_cmd(8, 0x1aa, 0x87);
    sd_dummy();              /* command version; reserved */
    sd_dummy();              /* reserved */
    uint8_t r4 = sd_dummy(); /* voltage */
    uint8_t r5 = sd_dummy(); /* check pattern */
    sd_dummy();

    sd_dummy(); // additional 0xff for good measure
    return r1 == 0x1 && (r4 & 0xf) == 0x1 && r5 == 0xaa;
}

int sd_cmd55()
{
    uint8_t r = sd_cmd(55, 0x0, 0x65);
    sd_dummy();
    print_status("cmd55", r);
    return r == 0x1;
}

int sd_acmd41()
{
    uint8_t r;
    do
    {
        sd_cmd55();
        r = sd_cmd(41, 0x40000000, 0x77); /* HCS = 1 */
        print_status("cmd41", r);
        sd_dummy();
    } while (r == 0x1);
    return (r == 0x00);
}

int init_sd()
{
    spi_init();

    print_uart("initializing SD... \r\n");
    // mostly taken from
    // https://electronics.stackexchange.com/questions/77417/what-is-the-correct-command-sequence-for-microsd-card-initialization-in-spi
    // and the siFive implementation:
    // https://github.com/sifive/freedom-u540-c000-bootloader/blob/09ac8c24dae741e6234e2b1e663784294367e147/sd/sd.c

    // send 10 bytes 0xff
    for (int i = 0; i < 10; i++)
        sd_dummy();

    if (!sd_cmd0())
        return SD_INIT_ERROR_CMD0;
    if (!sd_cmd8())
        return SD_INIT_ERROR_CMD8;
    if (!sd_acmd41())
        return SD_INIT_ERROR_ACMD41;
    return 0;
}

uint8_t crc7(uint8_t prev, uint8_t in)
{
    // CRC polynomial 0x89
    uint8_t remainder = prev & in;
    remainder ^= (remainder >> 4) ^ (remainder >> 7);
    remainder ^= remainder << 4;
    return remainder & 0x7f;
}

uint16_t crc16(uint16_t crc, uint8_t data)
{
    // CRC polynomial 0x11021
    crc = (uint8_t)(crc >> 8) | (crc << 8);
    crc ^= data;
    crc ^= (uint8_t)(crc >> 4) & 0xf;
    crc ^= crc << 12;
    crc ^= (crc & 0xff) << 5;
    return crc;
}

int sd_copy(void *dst, uint32_t src_lba, uint32_t size)
{
    volatile uint8_t *p = dst;
    long i = size;
    int rc = 0;

    uint8_t ff[128];
    for (int j = 0; j < 128; j++)
        ff[j] = 0xff;

    uint8_t crc = 0;
    crc = crc7(crc, 0x40 | SD_CMD_READ_BLOCK_MULTIPLE);
    crc = crc7(crc, (src_lba >> 24) & 0xff);
    crc = crc7(crc, (src_lba >> 16) & 0xff);
    crc = crc7(crc, (src_lba >> 8) & 0xff);
    crc = crc7(crc, src_lba & 0xff);
    crc = (crc << 1) | 1;
    if (sd_cmd(18, src_lba, crc) != 0x00)
    {
        for (int j = 0; j < 8; j++)
            sd_dummy();

        print_uart("could not read SD block\r\n");
        return -1;
    }
    do
    {
        uint16_t crc, crc_exp;
        long n;

        crc = 0;
        n = 512;
        while (sd_dummy() != SD_DATA_TOKEN)
            ;
        do
        {
            int bytes_per_transfer = 64;
            spi_write_bytes(ff, bytes_per_transfer, (uint8_t *)p);
            for (int i = 0; i < bytes_per_transfer; i++)
            {
                crc = crc16(crc, p[i]);
            }
            p += bytes_per_transfer;
            n -= bytes_per_transfer;
            // uint8_t x = sd_dummy();
            // *p++ = x;
            // crc = crc16(crc, x);
        } while (n > 0);

        crc_exp = ((uint16_t)sd_dummy() << 8);
        crc_exp |= sd_dummy();

        if (crc != crc_exp)
        {
            rc = SD_COPY_ERROR_CMD18_CRC;
            break;
        }
        if ((i % 1000) == 0)
        {
            print_uart(".");
        }
    } while (--i > 0);

    sd_cmd(SD_CMD_STOP_TRANSMISSION, 0, 0x01);
    sd_dummy();
    return rc;
}
