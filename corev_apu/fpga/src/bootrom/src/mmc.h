// Copyright (c) 2025 Thales Research and Technology
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
/**
 * \file mmc.h
 * \brief Contains all the symbols for the mmc commands.
 * \author Julien Mallet
 * 
*/

#ifndef MMC_H
#define MMC_H


#include "bootrom_types.h"

/* *************** DATA *************** */
#define MMC_DATA_READ		1


/* *************** VOLTAGE *************** */
#define MMC_VDD_32_33		0x00100000	/* VDD voltage 3.2 ~ 3.3 */
#define MMC_VDD_33_34		0x00200000	/* VDD voltage 3.3 ~ 3.4 */


/* *************** OCR *************** */
#define OCR_HCS			0x40000000
#define OCR_BUSY		0x80000000


/* *************** MMC STATUS *************** */
// #define MMC_STATUS_CURR_STATE	(0xf << 9)


/* *************** MMC CMD *************** */
#define MMC_CMD_GO_IDLE_STATE		0
#define MMC_CMD_ALL_SEND_CID		2
#define MMC_CMD_SELECT_CARD		7
#define MMC_CMD_SEND_CSD		9
#define MMC_CMD_STOP_TRANSMISSION	12
// #define MMC_CMD_SEND_STATUS		13
#define MMC_CMD_SET_BLOCKLEN		16
#define MMC_CMD_READ_SINGLE_BLOCK	17
#define MMC_CMD_READ_MULTIPLE_BLOCK	18
#define MMC_CMD_SET_BLOCK_COUNT		23


#define MMC_CMD_APP_CMD			55

// SD SPECIFIC
#define SD_CMD_SEND_RELATIVE_ADDR	3
// #define SD_CMD_APP_SET_BUS_WIDTH	6
#define SD_CMD_SEND_IF_COND		8
#define SD_CMD_APP_SEND_OP_COND		41
#define SD_CMD_APP_SEND_SCR		51


/* *************** MMC RESPONSE *************** */
#define MMC_RSP_PRESENT (1 << 0)
#define MMC_RSP_136	(1 << 1)		/* 136 bit response */
#define MMC_RSP_CRC	(1 << 2)		/* expect valid crc */
#define MMC_RSP_BUSY	(1 << 3)		/* card may send busy */
#define MMC_RSP_OPCODE	(1 << 4)		/* response contains opcode */

#define MMC_RSP_NONE	(0)
#define MMC_RSP_R1	(MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE)
#define MMC_RSP_R1b	(MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE| MMC_RSP_BUSY)
#define MMC_RSP_R2	(MMC_RSP_PRESENT|MMC_RSP_136|MMC_RSP_CRC)
#define MMC_RSP_R3	(MMC_RSP_PRESENT)
#define MMC_RSP_R4	(MMC_RSP_PRESENT)
#define MMC_RSP_R5	(MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE)
#define MMC_RSP_R6	(MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE)
#define MMC_RSP_R7	(MMC_RSP_PRESENT|MMC_RSP_CRC|MMC_RSP_OPCODE)


/* *************** MMC STORAGE *************** */

/* Maximum block size for MMC */
#define MMC_MAX_BLOCK_LEN	512


/* *************** MMC STRUCTURES  *************** */

struct mmc_cmd
{
	u8_t cmdidx;	 // Command index
	u32_t resp_type;	// Response type
	u32_t cmdarg;	   // Command argument
	u32_t response[4];  // Response array
};


struct mmc_data
{
	u8_t *dest;

	u32_t flags;
	u32_t blocks;
	u32_t blocksize;
};


struct sdhci_host_t
{
	u32_t dma_buf_addr; // addr of the buffer used by the dma
	u16_t rca; // relative card address
	u8_t bus_width;
};


/* *************** FUNCTIONS SIGNATURES *************** */


// MMC CMD
u8_t mmc_go_idle(volatile struct sdhci_host_t *g_dwc_mshc);
u8_t mmc_send_if_cond(volatile struct sdhci_host_t *g_dwc_mshc);
u8_t sd_send_op_cond(volatile struct sdhci_host_t *g_dwc_mshc);
u8_t mmc_send_cid(volatile struct sdhci_host_t *g_dwc_mshc);
u8_t sd_send_rca(volatile struct sdhci_host_t *g_dwc_mshc);
u8_t sd_send_csd(volatile struct sdhci_host_t *g_dwc_mshc);
u8_t sd_select_card(volatile struct sdhci_host_t *g_dwc_mshc);
u8_t sd_send_scr(volatile struct sdhci_host_t *g_dwc_mshc);
// u32_t mmc_send_status(volatile struct sdhci_host_t *g_dwc_mshc);
u8_t mmc_set_blocklen(volatile struct sdhci_host_t *g_dwc_mshc, u32_t len);
u8_t sd_copy(volatile struct sdhci_host_t *g_dwc_mshc, void *dst, u64_t src_lba, u64_t blkcnt);


#endif