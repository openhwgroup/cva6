/*-----------------------------------------------------------------------*/
/*  Low level disk interface module include file   (C)ChaN, 2014         */
/*-----------------------------------------------------------------------*/
/*
 *  Copyright (C) 2014, ChaN, all right reserved.
 *
 * * This software is a free software and there is NO WARRANTY.
 * * No restriction on use. You can use, modify and redistribute it for
 *   personal, non-profit or commercial products UNDER YOUR RESPONSIBILITY.
 * * Redistributions of source code must retain the above copyright notice.
 *
 * Copyright (c) 2015-2018, University of Cambridge.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University of Cambridge nor the
 *    names of its contributors may be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * IN NO EVENT SHALL UNIVERSITY OF CAMBRIDGE BE LIABLE TO ANY PARTY FOR DIRECT,
 * INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS,
 * ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS
 * HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * UNIVERSITY OF CAMBRIDGE SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT
 * NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY,
 * PROVIDED HEREUNDER IS PROVIDED "AS IS". UNIVERSITY OF CAMBRIDGE HAS NO
 * OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
 * MODIFICATIONS.
 */
/*------------------------------------------------------------------------*/

#ifndef _DISKIO_DEFINED
#define _DISKIO_DEFINED

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

#define _USE_WRITE  1   /* 1: Enable disk_write function */
#define _USE_IOCTL  1   /* 1: Enable disk_ioctl fucntion */

  /* Status of Disk Functions */
  typedef uint8_t    DSTATUS;

  /* Results of Disk Functions */
  typedef enum {
    RES_OK = 0,     /* 0: Successful */
    RES_ERROR,      /* 1: R/W Error */
    RES_WRPRT,      /* 2: Write Protected */
    RES_NOTRDY,     /* 3: Not Ready */
    RES_PARERR      /* 4: Invalid Parameter */
  } DRESULT;


  /*---------------------------------------*/
  /* Prototypes for disk control functions */

  uint8_t sd_send(uint8_t dat);
  void sd_init(void);
  void sd_disable(void) ;
  void sd_deselect (void);
  int sd_select (void);
  int rcvr_datablock (uint8_t *buff,uint32_t btr);
  int xmit_datablock (const uint8_t *buff, uint8_t token);
  uint8_t send_cmd (uint8_t cmd, uint32_t arg, uint32_t flag);
  DSTATUS disk_initialize (uint8_t pdrv);
  DSTATUS disk_status (uint8_t pdrv);
  DRESULT disk_read (uint8_t pdrv, uint8_t* buff, uint32_t sector, uint32_t count);
#if _USE_WRITE
  DRESULT disk_write (uint8_t pdrv, const uint8_t* buff, uint32_t sector, uint32_t count);
#endif
#if _USE_IOCTL
  DRESULT disk_ioctl (uint8_t pdrv, uint8_t cmd, void* buff);
#endif
  void disk_timerproc (void);
  void read_block(void *dst, int sect);

  /* Disk Status Bits (DSTATUS) */
#define STA_NOINIT      0x01    /* Drive not initialized */
#define STA_NODISK      0x02    /* No medium in the drive */
#define STA_PROTECT     0x04    /* Write protected */


  /* Command code for disk_ioctrl fucntion */

  /* Generic command (Used by FatFs) */
#define CTRL_SYNC           0   /* Complete pending write process (needed at _FS_READONLY == 0) */
#define GET_SECTOR_COUNT    1   /* Get media size (needed at _USE_MKFS == 1) */
#define GET_SECTOR_SIZE     2   /* Get sector size (needed at _MAX_SS != _MIN_SS) */
#define GET_BLOCK_SIZE      3   /* Get erase block size (needed at _USE_MKFS == 1) */
#define CTRL_TRIM           4   /* Inform device that the data on the block of sectors is no longer used (needed at _USE_TRIM == 1) */

  /* Generic command (Not used by FatFs) */
#define CTRL_FORMAT         5   /* Create physical format on the media */
#define CTRL_POWER_IDLE     6   /* Put the device idle state */
#define CTRL_POWER_OFF      7   /* Put the device off state */
#define CTRL_LOCK           8   /* Lock media removal */
#define CTRL_UNLOCK         9   /* Unlock media removal */
#define CTRL_EJECT          10  /* Eject media */

  /* MMC/SDC specific command (Not used by FatFs) */
#define MMC_GET_TYPE        50  /* Get card type */
#define MMC_GET_CSD         51  /* Get CSD */
#define MMC_GET_CID         52  /* Get CID */
#define MMC_GET_OCR         53  /* Get OCR */
#define MMC_GET_SDSTAT      54  /* Get SD status */

  /* ATA/CF specific command (Not used by FatFs) */
#define ATA_GET_REV         60  /* Get F/W revision */
#define ATA_GET_MODEL       61  /* Get model name */
#define ATA_GET_SN          62  /* Get serial number */


  /* MMC card type flags (MMC_GET_TYPE) */
#define CT_MMC      0x01        /* MMC ver 3 */
#define CT_SD1      0x02        /* SD ver 1 */
#define CT_SD2      0x04        /* SD ver 2 */
#define CT_SDC      (CT_SD1|CT_SD2) /* SD */
#define CT_BLOCK    0x08        /* Block addressing */

/* Definitions for MMC/SDC command */
#define CMD0    (0)         /* GO_IDLE_STATE */
#define CMD1    (1)         /* SEND_OP_COND (MMC) */
#define ACMD41  (0x80+41)   /* SEND_OP_COND (SDC) */
#define CMD8    (8)         /* SEND_IF_COND */
#define CMD9    (9)         /* SEND_CSD */
#define CMD10   (10)        /* SEND_CID */
#define CMD12   (12)        /* STOP_TRANSMISSION */
#define ACMD13  (0x80+13)   /* SD_STATUS (SDC) */
#define CMD16   (16)        /* SET_BLOCKLEN */
#define CMD17   (17)        /* READ_SINGLE_BLOCK */
#define CMD18   (18)        /* READ_MULTIPLE_BLOCK */
#define CMD23   (23)        /* SET_BLOCK_COUNT (MMC) */
#define ACMD23  (0x80+23)   /* SET_WR_BLK_ERASE_COUNT (SDC) */
#define CMD24   (24)        /* WRITE_BLOCK */
#define CMD25   (25)        /* WRITE_MULTIPLE_BLOCK */
#define CMD32   (32)        /* ERASE_ER_BLK_START */
#define CMD33   (33)        /* ERASE_ER_BLK_END */
#define CMD38   (38)        /* ERASE */
#define CMD55   (55)        /* APP_CMD */
#define CMD58   (58)        /* READ_OCR */

#define MMC_RSP_PRESENT (1 << 0)
#define MMC_RSP_136     (1 << 1)                /* 136 bit response */
#define MMC_RSP_CRC     (1 << 2)                /* expect valid crc */
#define MMC_RSP_BUSY    (1 << 3)                /* card may send busy */
#define MMC_RSP_OPCODE  (1 << 4)                /* response contains opcode */

#define MMC_RSP_NONE    (0)
#define MMC_RSP_R1      (MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE)
#define MMC_RSP_R1b     (MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE| \
                        MMC_RSP_BUSY)
#define MMC_RSP_R2      (MMC_RSP_PRESENT|MMC_RSP_136|MMC_RSP_CRC)
#define MMC_RSP_R3      (MMC_RSP_PRESENT)
#define MMC_RSP_R4      (MMC_RSP_PRESENT)
#define MMC_RSP_R5      (MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE)
#define MMC_RSP_R6      (MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE)
#define MMC_RSP_R7      (MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE)

#ifdef __cplusplus
}
#endif

#endif
