// See LICENSE for license details.

#include <stddef.h>
#include <stdint.h>
#include <memory.h>
#include "mini-printf.h"
#include "diskio.h"
#include "uart.h"
#include "lowrisc_pitonsd.h"

#define DUMP_REGS
#define SDBase      0x20000000
 
volatile uint64_t *const sd_base = (volatile uint64_t *)SDBase;
volatile uint64_t *const sd_bram = (volatile uint64_t *)(SDBase + 0x8000);

static inline void fence(void)
{
        asm volatile ("fence" ::: "memory");
}

static inline void fence_io(void)
{
        asm volatile ("fence io,io" ::: "memory");
}

#ifdef DUMP_REGS
static void pitonsd_dump_regs(void)
{
  static char init_state_num[10], tran_state_num[10];
  const char *init_state = init_state_num, *tran_state = tran_state_num;
  char status[99];
  int stat = sd_base[_piton_sd_STATUS];
  *status = 0;
  if (stat&1) strcat(status," REQ_RD");
  if (stat&2) strcat(status," REQ_WR");
  if (stat&4) strcat(status," IRQ_EN");
  if (stat&8) strcat(status," SD_IRQ");
  if (stat&16) strcat(status," REQ_RDY");
  if (stat&32) strcat(status," INIT_DONE");
  if (stat&64) strcat(status," HCXC");
  if (stat&128) strcat(status," DETECT");
#ifdef DUMP_REGS_VERBOSE
  switch(sd_base[_piton_sd_INIT_STATE])
    {
    case 0x0: init_state = "ST_CI_EN_SW_RST"; break;
    case 0x1: init_state = "ST_CI_DAT_TIMEOUT"; break;
    case 0x2: init_state = "ST_CI_BUS_WIDTH"; break;
    case 0x3: init_state = "ST_CI_CMD_TIMEOUT"; break;
    case 0x4: init_state = "ST_CI_CMD_ISER"; break;
    case 0x5: init_state = "ST_CI_DAT_ISER"; break;
    case 0x6: init_state = "ST_CI_BLK_SIZE"; break;
    case 0x7: init_state = "ST_CI_BLK_COUNT"; break;
    case 0x8: init_state = "ST_CI_CLOCK_DIV"; break;
    case 0x9: init_state = "ST_CI_DE_SW_RST"; break;
    case 0xa: init_state = "ST_CI_WAIT_POWER"; break;

    case 0x10: init_state = "ST_CMD0_CLR_CMD_ISR"; break;
    case 0x11: init_state = "ST_CMD0_WAIT_CLR"; break;
    case 0x12: init_state = "ST_CMD0_CMD"; break;
    case 0x13: init_state = "ST_CMD0_ARG"; break;
    case 0x14: init_state = "ST_CMD0_WAIT_INT"; break;
    case 0x15: init_state = "ST_CMD0_RD_CMD_ISR"; break;

    case 0x20: init_state = "ST_CMD8_CLR_CMD_ISR"; break;
    case 0x21: init_state = "ST_CMD8_WAIT_CLR"; break;
    case 0x22: init_state = "ST_CMD8_CMD"; break;
    case 0x23: init_state = "ST_CMD8_ARG"; break;
    case 0x24: init_state = "ST_CMD8_WAIT_INT"; break;
    case 0x25: init_state = "ST_CMD8_RD_CMD_ISR"; break;
    case 0x26: init_state = "ST_CMD8_RD_RESP0"; break;

    case 0x30: init_state = "ST_ACMD41_CMD55_CLR_CMD_ISR"; break;
    case 0x31: init_state = "ST_ACMD41_CMD55_WAIT_CLR"; break;
    case 0x32: init_state = "ST_ACMD41_CMD55_CMD"; break;
    case 0x33: init_state = "ST_ACMD41_CMD55_ARG"; break;
    case 0x34: init_state = "ST_ACMD41_CMD55_WAIT_INT"; break;
    case 0x35: init_state = "ST_ACMD41_CMD55_RD_CMD_ISR"; break;
    case 0x36: init_state = "ST_ACMD41_CMD55_RD_RESP0"; break;

    case 0x40: init_state = "ST_ACMD41_CLR_CMD_ISR"; break;
    case 0x41: init_state = "ST_ACMD41_WAIT_CLR"; break;
    case 0x42: init_state = "ST_ACMD41_CMD"; break;
    case 0x43: init_state = "ST_ACMD41_ARG"; break;
    case 0x44: init_state = "ST_ACMD41_WAIT_INT"; break;
    case 0x45: init_state = "ST_ACMD41_RD_CMD_ISR"; break;
    case 0x46: init_state = "ST_ACMD41_RD_RESP0"; break;
    case 0x47: init_state = "ST_ACMD41_WAIT_INTERVAL"; break;

    case 0x50: init_state = "ST_CMD2_CLR_CMD_ISR"; break;
    case 0x51: init_state = "ST_CMD2_WAIT_CLR"; break;
    case 0x52: init_state = "ST_CMD2_CMD"; break;
    case 0x53: init_state = "ST_CMD2_ARG"; break;
    case 0x54: init_state = "ST_CMD2_WAIT_INT"; break;
    case 0x55: init_state = "ST_CMD2_RD_CMD_ISR"; break;

    case 0x60: init_state = "ST_CMD3_CLR_CMD_ISR"; break;
    case 0x61: init_state = "ST_CMD3_WAIT_CLR"; break;
    case 0x62: init_state = "ST_CMD3_CMD"; break;
    case 0x63: init_state = "ST_CMD3_ARG"; break;
    case 0x64: init_state = "ST_CMD3_WAIT_INT"; break;
    case 0x65: init_state = "ST_CMD3_RD_CMD_ISR"; break;
    case 0x66: init_state = "ST_CMD3_RD_RESP0"; break;

    case 0x70: init_state = "ST_HS_EN_SW_RST"; break;
    case 0x71: init_state = "ST_HS_CLOCK_DIV"; break;
    case 0x72: init_state = "ST_HS_DE_SW_RST"; break;

    case 0x80: init_state = "ST_CMD7_CLR_CMD_ISR"; break;
    case 0x81: init_state = "ST_CMD7_WAIT_CLR"; break;
    case 0x82: init_state = "ST_CMD7_CMD"; break;
    case 0x83: init_state = "ST_CMD7_ARG"; break;
    case 0x84: init_state = "ST_CMD7_WAIT_INT"; break;
    case 0x85: init_state = "ST_CMD7_RD_CMD_ISR"; break;
    case 0x86: init_state = "ST_CMD7_RD_RESP0"; break;

    case 0x90: init_state = "ST_ACMD6_CMD55_CLR_CMD_ISR"; break;
    case 0x91: init_state = "ST_ACMD6_CMD55_WAIT_CLR"; break;
    case 0x92: init_state = "ST_ACMD6_CMD55_CMD"; break;
    case 0x93: init_state = "ST_ACMD6_CMD55_ARG"; break;
    case 0x94: init_state = "ST_ACMD6_CMD55_WAIT_INT"; break;
    case 0x95: init_state = "ST_ACMD6_CMD55_RD_CMD_ISR"; break;
    case 0x96: init_state = "ST_ACMD6_CMD55_RD_RESP0"; break;

    case 0xa0: init_state = "ST_ACMD6_CLR_CMD_ISR"; break;
    case 0xa1: init_state = "ST_ACMD6_WAIT_CLR"; break;
    case 0xa2: init_state = "ST_ACMD6_CMD"; break;
    case 0xa3: init_state = "ST_ACMD6_ARG"; break;
    case 0xa4: init_state = "ST_ACMD6_WAIT_INT"; break;
    case 0xa5: init_state = "ST_ACMD6_RD_CMD_ISR"; break;
    case 0xa6: init_state = "ST_ACMD6_RD_RESP0"; break;

    case 0xb0: init_state = "ST_FIN_CLR_CMD_ISR"; break;
    case 0xb1: init_state = "ST_FIN_CLR_DAT_ISR"; break;

    case 0xf0: init_state = "ST_INIT_DONE"; break;
    case 0xff: init_state = "ST_INIT_ERR"; break;
    default: init_state = "UNKNOWN";
    }
#else
  sprintf(init_state_num, "0x%lx", sd_base[_piton_sd_INIT_STATE]);
#endif  
#ifdef DUMP_REGS_VERBOSE
  switch(sd_base[_piton_sd_TRAN_STATE])
    {
    case 0x3f: tran_state = "ST_RST"; break;

    case 0x00: tran_state = "ST_IDLE"; break;
    case 0x01: tran_state = "ST_OK_RESP_PENDING"; break;
    case 0x02: tran_state = "ST_ERR_RESP_PENDING"; break;
    case 0x03: tran_state = "ST_CLR_CMD_ISR"; break;
    case 0x04: tran_state = "ST_CLR_DAT_ISR"; break;

    case 0x10: tran_state = "ST_CMD17_DMA"; break;
    case 0x11: tran_state = "ST_CMD17_CMD"; break;
    case 0x12: tran_state = "ST_CMD17_WAIT_CLR"; break;
    case 0x13: tran_state = "ST_CMD17_ARG"; break;
    case 0x14: tran_state = "ST_CMD17_WAIT_CMD_INT"; break;
    case 0x15: tran_state = "ST_CMD17_RD_CMD_ISR"; break;
    case 0x16: tran_state = "ST_CMD17_RD_RESP0"; break;
    case 0x17: tran_state = "ST_CMD17_WAIT_DATA_INT"; break;
    case 0x18: tran_state = "ST_CMD17_RD_DATA_ISR"; break;

    case 0x20: tran_state = "ST_CMD24_DMA"; break;
    case 0x21: tran_state = "ST_CMD24_CMD"; break;
    case 0x22: tran_state = "ST_CMD24_WAIT_CLR"; break;
    case 0x23: tran_state = "ST_CMD24_ARG"; break;
    case 0x24: tran_state = "ST_CMD24_WAIT_CMD_INT"; break;
    case 0x25: tran_state = "ST_CMD24_RD_CMD_ISR"; break;
    case 0x26: tran_state = "ST_CMD24_RD_RESP0"; break;
    case 0x27: tran_state = "ST_CMD24_WAIT_DATA_INT"; break;
    case 0x28: tran_state = "ST_CMD24_RD_DATA_ISR"; break;
    default: tran_state = "UNKNOWN";
    }
#else
  sprintf(tran_state_num, "0x%lx", sd_base[_piton_sd_TRAN_STATE]);
#endif  
  printf(
        "    sd_f:  0x%lx  dma_f: 0x%lx status: %s\n"
        "    resp_vec: 0x%lx  init_state: %s  counter: 0x%lx\n"
        "    init_fsm: 0x%lx  tran_state: %s  tran_fsm: 0x%lx\n",
        sd_base[_piton_sd_ADDR_SD_F],
        sd_base[_piton_sd_ADDR_DMA_F],
        status,
        sd_base[_piton_sd_ERROR],
        init_state,
        sd_base[_piton_sd_COUNTER],
        sd_base[_piton_sd_INIT_FSM],
        tran_state,
        sd_base[_piton_sd_TRAN_FSM]);
}
#endif

DSTATUS disk_initialize (uint8_t pdrv)
{
        int old_init_state = -1;
        /* SD sector address */
        sd_base[ _piton_sd_ADDR_SD ] = 0;
        /* always start at beginning of DMA buffer */
        sd_base[ _piton_sd_ADDR_DMA ] = 0;
        /* set sector count */
        sd_base[ _piton_sd_BLKCNT ] = 0;
        sd_base[ _piton_sd_REQ_RD ] = 0;
        sd_base[ _piton_sd_REQ_WR ] = 0;
        sd_base[ _piton_sd_IRQ_EN ] = 0;
        sd_base[ _piton_sd_SYS_RST ] = 0;

        /* reset HW state machine */
        sd_base[ _piton_sd_SYS_RST ] = 1;
        fence_io();
        do
          {
            int init_state = sd_base[_piton_sd_INIT_STATE];
#ifdef DUMP_REGS_VERBOSE
            printf("init_state = 0x%x\n", init_state);
#endif
#ifdef DUMP_REGS
            if (old_init_state != init_state)
              pitonsd_dump_regs();
#endif
            old_init_state = init_state;
          }
          while (old_init_state != 0xf0);
#ifdef DUMP_REGS
        pitonsd_dump_regs();
#endif
        return 0;
}

DRESULT disk_read (uint8_t pdrv, uint8_t *buff, uint32_t sector, uint32_t count)
{
  uint64_t vec;
#ifdef DUMP_REGS_VERBOSE
  uint64_t stat2;
#endif
  uint64_t stat = 0xDEADBEEF;
  uint64_t mask = (1 << count) - 1;
  /* SD sector address */
  sd_base[ _piton_sd_ADDR_SD ] = sector;
  /* always start at beginning of DMA buffer */
  sd_base[ _piton_sd_ADDR_DMA ] = 0;
  /* set sector count */
  sd_base[ _piton_sd_BLKCNT ] = count;
  sd_base[ _piton_sd_REQ_RD ] = 1;
  fence_io();
#ifdef DUMP_REGS_VERBOSE
  printf("disk_read(0x%x, 0x%x, 0x%x, 0x%x);\n", pdrv, buff, sector, count);
#endif
  do
    {
#ifdef ISSUE_356
      fence(); /* This is needed for a suspected Ariane bug */
#endif      
      stat = sd_base[_piton_sd_STATUS];
#ifdef DUMP_REGS_VERBOSE
      stat2 = sd_base[_piton_sd_STATUS+32];
      printf("stat = 0x%x, stat2 = 0x%x\n", stat, stat2);
#endif
    }
  while (_piton_sd_STATUS_REQ_RDY & ~stat);
  sd_base[ _piton_sd_REQ_RD ] = 0;
  vec = sd_base[ _piton_sd_ERROR ] & mask;
  memcpy(buff, (void *)sd_bram, count*512);
  if (vec==mask)
    return 0;
#ifdef DUMP_REGS
  pitonsd_dump_regs();
#endif  
  return -1;
}

