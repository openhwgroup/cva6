// Copyright OpenHW Group contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "gpt.h"

#include "sd.h"
#include "uart.h"
#include <stddef.h>

int gpt_find_boot_partition(uint8_t* dest, uint32_t size)
{
    int ret = init_sd();
    if (ret != 0) {
        print_uart("could not initialize sd... exiting\r\n");
        return -1;
    }

    print_uart("sd initialized!\r\n");

    // load LBA1
    size_t block_size = 512;
    uint8_t lba1_buf[block_size];

    int res = sd_copy(lba1_buf, 1, 1);

    if (res != 0)
    {
        print_uart("SD card failed!\r\n");
        print_uart("sd copy return value: ");
        print_uart_addr(res);
        print_uart("\r\n");
        return -2;
    }

    gpt_pth_t *lba1 = (gpt_pth_t *)lba1_buf;

    print_uart("gpt partition table header:");
    print_uart("\r\n\tsignature:\t");
    print_uart_addr(lba1->signature);
    print_uart("\r\n\trevision:\t");
    print_uart_int(lba1->revision);
    print_uart("\r\n\tsize:\t\t");
    print_uart_int(lba1->header_size);
    print_uart("\r\n\tcrc_header:\t");
    print_uart_int(lba1->crc_header);
    print_uart("\r\n\treserved:\t");
    print_uart_int(lba1->reserved);
    print_uart("\r\n\tcurrent lba:\t");
    print_uart_addr(lba1->current_lba);
    print_uart("\r\n\tbackup lda:\t");
    print_uart_addr(lba1->backup_lba);
    print_uart("\r\n\tpartition entries lba:   \t");
    print_uart_addr(lba1->partition_entries_lba);
    print_uart("\r\n\tnumber partition entries:\t");
    print_uart_int(lba1->nr_partition_entries);
    print_uart("\r\n\tsize partition entries:  \t");
    print_uart_int(lba1->size_partition_entry);
    print_uart("\r\n");

    uint8_t lba2_buf[block_size];

    res = sd_copy(lba2_buf, lba1->partition_entries_lba, 1);

    if (res != 0)
    {
        print_uart("SD card failed!\r\n");
        print_uart("sd copy return value: ");
        print_uart_addr(res);
        print_uart("\r\n");
        return -2;
    }

    for (int i = 0; i < 4; i++)
    {
        partition_entries_t *part_entry = (partition_entries_t *)(lba2_buf + (i * 128));
        print_uart("gpt partition entry ");
        print_uart_byte(i);
        print_uart("\r\n\tpartition type guid:\t");
        for (int j = 0; j < 16; j++)
            print_uart_byte(part_entry->partition_type_guid[j]);
        print_uart("\r\n\tpartition guid:     \t");
        for (int j = 0; j < 16; j++)
            print_uart_byte(part_entry->partition_guid[j]);
        print_uart("\r\n\tfirst lba:\t");
        print_uart_addr(part_entry->first_lba);
        print_uart("\r\n\tlast lba:\t");
        print_uart_addr(part_entry->last_lba);
        print_uart("\r\n\tattributes:\t");
        print_uart_addr(part_entry->attributes);
        print_uart("\r\n\tname:\t");
        for (int j = 0; j < 72; j++)
            print_uart_byte(part_entry->name[j]);
        print_uart("\r\n");
    }

    partition_entries_t *boot = (partition_entries_t *)(lba2_buf);
    print_uart("copying boot image ");
    res = sd_copy(dest, boot->first_lba, boot->last_lba - boot->first_lba + 1);

    if (res != 0)
    {
        print_uart("SD card failed!\r\n");
        print_uart("sd copy return value: ");
        print_uart_addr(res);
        print_uart("\r\n");
        return -2;
    }

    print_uart(" done!\r\n");
    return 0;
}
