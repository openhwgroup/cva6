// Copyright OpenHW Group contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <stdint.h>

#define SD_CMD_STOP_TRANSMISSION 12
#define SD_CMD_READ_BLOCK_MULTIPLE 18
#define SD_DATA_TOKEN 0xfe
#define SD_COPY_ERROR_CMD18 -1
#define SD_COPY_ERROR_CMD18_CRC -2

// errors
#define SD_INIT_ERROR_CMD0 -1
#define SD_INIT_ERROR_CMD8 -2
#define SD_INIT_ERROR_ACMD41 -3

int init_sd();

void put_sdcard_spi_mode();

int sd_copy(void *dst, uint32_t src_lba, uint32_t size);
