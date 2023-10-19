// Copyright OpenHW Group contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <stdint.h>

// LBA 0: Protective MBR
// ignored here

// Partition Table Header (LBA 1)
typedef struct gpt_pth
{
    uint64_t signature;
    uint32_t revision;
    uint32_t header_size; //! little endian, usually 0x5c = 92
    uint32_t crc_header;
    uint32_t reserved; //! must be 0
    uint64_t current_lba;
    uint64_t backup_lba;
    uint64_t first_usable_lba;
    uint64_t last_usable_lba;
    uint8_t disk_guid[16];
    uint64_t partition_entries_lba;
    uint32_t nr_partition_entries;
    uint32_t size_partition_entry; //! usually 0x80 = 128
    uint32_t crc_partition_entry;
} gpt_pth_t;

// Partition Entries (LBA 2-33)
typedef struct partition_entries
{
    uint8_t partition_type_guid[16];
    uint8_t partition_guid[16];
    uint64_t first_lba;
    uint64_t last_lba; //! inclusive
    uint64_t attributes;
    uint8_t name[72]; //! utf16 encoded
} partition_entries_t;

// Find boot partition and load it to the destination
int gpt_find_boot_partition(uint8_t* dest, uint32_t size);
