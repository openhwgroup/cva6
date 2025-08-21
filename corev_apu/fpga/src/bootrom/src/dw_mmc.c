// SPDX-License-Identifier: GPL-2.0+
/*
 * (C) Copyright 2012 SAMSUNG Electronics
 * Jaehoon Chung <jh80.chung@samsung.com>
 * Rajeshawari Shinde <rajeshwari.s@samsung.com>
 */



#include "bootrom_time.h"
#include "uart.h"
#include "dwmmc.h"
#include "cache.h"
#include "bouncebuf.h"
#include "memalign.h"
// #include "wait_bit.h"

#define PAGE_SIZE 4096
#define FIFO_MODE 1

void write_print(u32_t print,u32_t address, u32_t val){
	writel(val,MMC_BASE_ADDR+address);
	if (print){
		print_uart("WRITE L ADDR: ");
		print_uart_int(MMC_BASE_ADDR+address);
		print_uart(" DATA: ");
		print_uart_int(val);
		print_uart( "\n");
	}

	if(MMC_BASE_ADDR+address == 0x80000000UL){

		print_uart("WRITING TO FIRST ADDRESS: ");
		print_uart("WRITE L ADDR: ");
		print_uart_int(MMC_BASE_ADDR+address);
		print_uart(" DATA: ");
		print_uart_int(val);
		print_uart( "\n");
	}
	
}

u32_t read_print(u32_t print, u32_t address){
	u32_t val = readl(MMC_BASE_ADDR+address);
	if (print){
		print_uart("READ L ADDR: ");
		print_uart_int(MMC_BASE_ADDR+address);
		print_uart("DATA: ");
		print_uart_int(val);
		print_uart( "\n");
	}
	return val;
}
static int dwmci_wait_reset(u32_t value)
{
	unsigned long timeout = 1000;
	u32_t ctrl;

	write_print(0, DWMCI_CTRL, value);

	while (timeout--) {
		ctrl = read_print(0, DWMCI_CTRL);
		if (!(ctrl & DWMCI_RESET_ALL))
			return 1;
	}
	return 0;
}

static void dwmci_set_idma_desc(struct dwmci_idmac *idmac,
		u32_t desc0, u32_t desc1, u32_t desc2)
{
	struct dwmci_idmac *desc = idmac;

	desc->flags = desc0;
	desc->cnt = desc1;
	desc->addr = desc2;
	desc->next_addr = (unsigned long)desc + sizeof(struct dwmci_idmac);
	print_uart("descriptor pointer address: ");
	print_uart_int(desc);
	print_uart("set descriptor: flags ");
	print_uart_int(desc->flags);
	print_uart(" cnt ");
	print_uart_int(desc->cnt);
	print_uart(" addr ");
	print_uart_int(desc->addr);
	print_uart(" next_addr ");
	print_uart_int(desc->next_addr);
	print_uart("\n");
}

static void dwmci_prepare_data(struct mmc_data *data,
			       struct dwmci_idmac *cur_idmac,
			       void *bounce_buffer)
{
	unsigned long ctrl;
	unsigned int i = 0, flags, cnt, blk_cnt;
	unsigned long data_start, data_end;


	blk_cnt = data->blocks;

	dwmci_wait_reset(DWMCI_CTRL_FIFO_RESET);

	/* Clear IDMAC interrupt */
	write_print(0, DWMCI_IDSTS, 0xFFFFFFFF);

	data_start = (unsigned long)cur_idmac;
	write_print(0, DWMCI_DBADDR, (unsigned long)cur_idmac);

	do {
		flags = DWMCI_IDMAC_OWN | DWMCI_IDMAC_CH ;
		flags |= (i == 0) ? DWMCI_IDMAC_FS : 0;
		if (blk_cnt <= 8) {
			flags |= DWMCI_IDMAC_LD;
			cnt = data->blocksize * blk_cnt;
		} else
			cnt = data->blocksize * 8;

		dwmci_set_idma_desc(cur_idmac, flags, cnt,
				    (unsigned long)bounce_buffer + (i * PAGE_SIZE));

		cur_idmac++;
		if (blk_cnt <= 8)
			break;
		blk_cnt -= 8;
		i++;
	} while(1);

	print_uart("prepare data, skipping flush! \n");
	// data_end = (unsigned long)cur_idmac;
	// flush_dcache_range(data_start, roundup(data_end, ARCH_DMA_MINALIGN));

	ctrl = read_print(1, DWMCI_CTRL);
	ctrl |= DWMCI_IDMAC_EN | DWMCI_DMA_EN;
	write_print(0, DWMCI_CTRL, ctrl);

	ctrl = read_print(1, DWMCI_BMOD);
	ctrl |= DWMCI_BMOD_IDMAC_FB | DWMCI_BMOD_IDMAC_EN;
	write_print(0, DWMCI_BMOD, ctrl);

	write_print(0, DWMCI_BLKSIZ, data->blocksize);
	write_print(0, DWMCI_BYTCNT, data->blocksize * data->blocks);
}

static int dwmci_fifo_ready(u32_t bit, u32_t *len)
{
	u32_t timeout = 20000;
	// print_uart(" fifo ready get len: ");
	*len = read_print(0, DWMCI_STATUS);
	while (--timeout && (*len & bit)) {
		udelay(200);
		print_uart(" fifo ready get len inside while : ");
		*len = read_print(1, DWMCI_STATUS);
	}

	if (!timeout) {
		print_uart("FIFO underflow timeout\n");
		return -ETIMEDOUT;
	}

	return 0;
}

// static unsigned int dwmci_get_timeout(struct mmc *mmc, const unsigned int size)
// {
// 	unsigned int timeout;

// 	timeout = size * 8;	/* counting in bits */
// 	timeout *= 10;		/* wait 10 times as long */
// 	timeout /= mmc->clock;
// 	timeout /= mmc->bus_width;
// 	timeout /= mmc->ddr_mode ? 2 : 1;
// 	timeout *= 1000;	/* counting in msec */
// 	timeout = (timeout < 1000) ? 1000 : timeout;

// 	return timeout;
// }

static int dwmci_data_transfer(struct mmc_data *data)
{
	int ret = 0;
	u32_t timeout, mask, size, i, len = 0;
	u32_t *buf = NULL;
	// unsigned long start = get_timer(0);
	// u32_t fifo_depth = (((host->fifoth_val & RX_WMARK_MASK) >>
	// 		    RX_WMARK_SHIFT) + 1) * 2;

	size = data->blocksize * data->blocks;
	// if (data->flags == MMC_DATA_READ)
		buf = (unsigned int *)data->dest;
	// else
	// 	buf = (unsigned int *)data->src;

	timeout = 1000000;

	size /= 4;
	read_print(0,DWMCI_STATUS);
	for (;;) {
		mask = read_print(0, DWMCI_RINTSTS);
		int val = read_print(0,DWMCI_STATUS);
		// if(val & 0x4)
		// 	print_uart("FIFO empty \n");
		/* Error during data transfer. */
		if (mask & (DWMCI_DATA_ERR | DWMCI_DATA_TOUT)) {
			print_uart("DATA ERROR!\n");
			ret = -EINVAL;
			return ret;
			// break;
		}
		
		// print_uart("size ");
		// print_uart_int(size);
		// print_uart("\n");
		
		if (FIFO_MODE && size!=0) {
			// print_uart("FIFO_MODE && size \n");
			len = 0;
			if (data->flags == MMC_DATA_READ &&
			    (mask & (DWMCI_INTMSK_RXDR | DWMCI_INTMSK_DTO))) {
				write_print(0, DWMCI_RINTSTS,
					     mask & (DWMCI_INTMSK_RXDR |
						     DWMCI_INTMSK_DTO));
				while (size) {
					ret = dwmci_fifo_ready(	DWMCI_FIFO_EMPTY,
							&len);
					if (ret < 0)
						break;

					len = (len >> DWMCI_FIFO_SHIFT) &
						    DWMCI_FIFO_MASK;
					len = min(size, len);
					// print_uart("actually reading! to ");
					// print_uart_int(buf);
					// print_uart("\n");

					// print_uart("size ");
					// print_uart_int(size);
					// print_uart("\n");

					// print_uart("len ");
					// print_uart_int(len);
					// print_uart("\n");
					
					for (i = 0; i < len; i++)
						*buf++ =
						read_print(0, DWMCI_DATA);
					size = size > len ? (size - len) : 0;
					// print_uart("finished reading! to ");
					// print_uart_int(buf);
					// print_uart("\n");
					// print_uart("remaining size ");
					// print_uart_int(size);
					// print_uart("\n");
				}
			} // else if (data->flags == MMC_DATA_WRITE &&
			// 	   (mask & DWMCI_INTMSK_TXDR)) {
			// 	while (size) {
			// 		ret = dwmci_fifo_ready(host,
			// 				DWMCI_FIFO_FULL,
			// 				&len);
			// 		if (ret < 0)
			// 			break;

			// 		len = fifo_depth - ((len >>
			// 			   DWMCI_FIFO_SHIFT) &
			// 			   DWMCI_FIFO_MASK);
			// 		len = min(size, len);
			// 		for (i = 0; i < len; i++)
			// 			write_print(0, DWMCI_DATA,
			// 				     *buf++);
			// 		size = size > len ? (size - len) : 0;
			// 	}
			// 	write_print(0, DWMCI_RINTSTS,
			// 		     DWMCI_INTMSK_TXDR);
			// }
		}

		/* Data arrived correctly. */
		if (mask & DWMCI_INTMSK_DTO) {
			ret = 0;
			break;
		}

		/* Check for timeout. */
		if (timeout-- > 0) {
			udelay(10);
		}
		else {
			read_print(1,DWMCI_STATUS);
			print_uart("Timeout waiting for data!\n");
			ret = -ETIMEDOUT;
			break;
		}
	}

	write_print(0, DWMCI_RINTSTS, mask);

	return ret;
}

static int dwmci_set_transfer_mode()
{
	unsigned long mode;

	mode = DWMCI_CMD_DATA_EXP;
	// if (data->flags & MMC_DATA_WRITE)
	// 	mode |= DWMCI_CMD_RW;

	return mode;
}


static int dwmci_send_cmd(struct mmc_cmd *cmd,
		struct mmc_data *data)
{

	struct dwmci_idmac *cur_idmac = (struct dwmci_idmac *) (0xFFE30000);

	// ALLOC_CACHE_ALIGN_BUFFER(struct dwmci_idmac, cur_idmac,
				//  data ? DIV_ROUND_UP(data->blocks, 8) : 0);
	int ret = 0, flags = 0, i;
	unsigned int timeout = 500;
	u32_t retry = 100000;
	u32_t mask, ctrl,reg;
	// unsigned long start = get_timer(0);
	struct bounce_buffer bbstate;

	while (read_print(0, DWMCI_STATUS) & DWMCI_BUSY) {
		if (timeout-- > 0)
		{
			udelay(10);
		}
		else {
			read_print(1, DWMCI_STATUS);
			print_uart("Timeout on data busy, continue anyway\n");
			break;
		}
	}

	write_print(0, DWMCI_RINTSTS, DWMCI_INTMSK_ALL);

	if (data) {
		if (FIFO_MODE) {
			write_print(0, DWMCI_BLKSIZ, data->blocksize);
			write_print(0, DWMCI_BYTCNT,
				     data->blocksize * data->blocks);
			dwmci_wait_reset(DWMCI_CTRL_FIFO_RESET);
		} else {
		// 	if (data->flags == MMC_DATA_READ) {
				ret = bounce_buffer_start(&bbstate,
						(void*)data->dest,
						data->blocksize *
						data->blocks, GEN_BB_WRITE);
			// } else {
			// 	ret = bounce_buffer_start(&bbstate,
			// 			(void*)data->src,
			// 			data->blocksize *
			// 			data->blocks, GEN_BB_READ);
			// }

			if (ret)
				return ret;

			dwmci_prepare_data(data, cur_idmac,
					   bbstate.bounce_buffer);
		}
	}

	write_print(0, DWMCI_CMDARG, cmd->cmdarg);

	if (data)
		flags = dwmci_set_transfer_mode();

	if ((cmd->resp_type & MMC_RSP_136) && (cmd->resp_type & MMC_RSP_BUSY))
		return -EBUSY;

	if (cmd->cmdidx == MMC_CMD_STOP_TRANSMISSION)
		flags |= DWMCI_CMD_ABORT_STOP;
	else
		flags |= DWMCI_CMD_PRV_DAT_WAIT;

	if (cmd->resp_type & MMC_RSP_PRESENT) {
		flags |= DWMCI_CMD_RESP_EXP;
		if (cmd->resp_type & MMC_RSP_136)
			flags |= DWMCI_CMD_RESP_LENGTH;
	}

	if (cmd->resp_type & MMC_RSP_CRC)
		flags |= DWMCI_CMD_CHECK_CRC;

	flags |= (cmd->cmdidx | DWMCI_CMD_START | DWMCI_CMD_USE_HOLD_REG);

	// print_uart("Sending CMD\n");

	write_print(0, DWMCI_CMD, flags);

	for (i = 0; i < retry; i++) {
		mask = read_print(0, DWMCI_RINTSTS);
		if (mask & DWMCI_INTMSK_CDONE) {
			if (!data)
				write_print(0, DWMCI_RINTSTS, mask);
			break;
		}
	}

	if (i == retry) {
		print_uart("Timeout. RINTSTS: ");
		print_uart_int(mask);
		print_uart("\n");
		
		return -ETIMEDOUT;
	}

	if (mask & DWMCI_INTMSK_RTO) {
		/*
		 * Timeout here is not necessarily fatal. (e)MMC cards
		 * will splat here when they receive CMD55 as they do
		 * not support this command and that is exactly the way
		 * to tell them apart from SD cards. Thus, this output
		 * below shall be debug(). eMMC cards also do not favor
		 * CMD8, please keep that in mind.
		 */
		print_uart("Response Timeout.\n");
		return -ETIMEDOUT;
	} else if (mask & DWMCI_INTMSK_RE) {
		print_uart("Response Error.\n");
		return -EIO;
	} else if ((cmd->resp_type & MMC_RSP_CRC) &&
		   (mask & DWMCI_INTMSK_RCRC)) {
		print_uart("Response CRC Error.\n");
		return -EIO;
	}


	if (cmd->resp_type & MMC_RSP_PRESENT) {
		if (cmd->resp_type & MMC_RSP_136) {
			cmd->response[0] = read_print(0, DWMCI_RESP3);
			cmd->response[1] = read_print(0, DWMCI_RESP2);
			cmd->response[2] = read_print(0, DWMCI_RESP1);
			cmd->response[3] = read_print(0, DWMCI_RESP0);
		} else {
			cmd->response[0] = read_print(0, DWMCI_RESP0);
		}
	}

	if (data) {
		ret = dwmci_data_transfer(data);

		/* only dma mode need it */
		if (!FIFO_MODE) {
		// 	if (data->flags == MMC_DATA_READ)
				mask = DWMCI_IDINTEN_RI;
			// else
			// 	mask = DWMCI_IDINTEN_TI;

			timeout = 1000;
			ret = 1;

			while(timeout-- > 0){
				reg = read_print(0,DWMCI_IDSTS);
				if ((reg & mask) == mask){
					ret = 0;
					break;
				}
					
				udelay(10);
			}
			// ret = wait_for_bit_le32(MMC_BASE_ADDR + DWMCI_IDSTS,
			// 			mask, true, 1000, false);
			if (ret){
				print_uart_int(reg);
				print_uart(" DWMCI_IDINTEN mask  timeout.\n");
				return ret;
			}
			/* clear interrupts */
			write_print(0, DWMCI_IDSTS, DWMCI_IDINTEN_MASK);

			ctrl = read_print(1, DWMCI_CTRL);
			ctrl &= ~(DWMCI_DMA_EN);
			write_print(0, DWMCI_CTRL, ctrl);
			bounce_buffer_stop(&bbstate);
		}
	}

	udelay(100);

	return ret;
}

// static int dwmci_setup_bus(struct dwmci_host *host, u32_t freq)
// {
// 	u32_t div, status;
// 	int timeout = 10000;
// 	unsigned long sclk;

// 	if ((freq == host->clock) || (freq == 0))
// 		return 0;
// 	/*
// 	 * If host->get_mmc_clk isn't defined,
// 	 * then assume that host->bus_hz is source clock value.
// 	 * host->bus_hz should be set by user.
// 	 */
// 	if (host->get_mmc_clk)
// 		sclk = host->get_mmc_clk(host, freq);
// 	else if (host->bus_hz)
// 		sclk = host->bus_hz;
// 	else {
// 		print_uart("Didn't get source clock value.\n");
// 		return -EINVAL;
// 	}

// 	if (sclk == freq)
// 		div = 0;	/* bypass mode */
// 	else
// 		div = DIV_ROUND_UP(sclk, 2 * freq);

// 	dwmci_write_print(0,host, DWMCI_CLKENA, 0);
// 	dwmci_write_print(0,host, DWMCI_CLKSRC, 0);

// 	dwmci_write_print(0,host, DWMCI_CLKDIV, div);
// 	dwmci_write_print(0,host, DWMCI_CMD, DWMCI_CMD_PRV_DAT_WAIT |
// 			DWMCI_CMD_UPD_CLK | DWMCI_CMD_START);

// 	do {
// 		status = read_print(0,MMC_BASE_ADDR + DWMCI_CMD);
// 		if (timeout-- < 0) {
// 			print_uart("Timeout!\n");
// 			return -ETIMEDOUT;
// 		}
// 	} while (status & DWMCI_CMD_START);

// 	dwmci_write_print(0,host, DWMCI_CLKENA, DWMCI_CLKEN_ENABLE |
// 			DWMCI_CLKEN_LOW_PWR);

// 	dwmci_write_print(0,host, DWMCI_CMD, DWMCI_CMD_PRV_DAT_WAIT |
// 			DWMCI_CMD_UPD_CLK | DWMCI_CMD_START);

// 	timeout = 10000;
// 	do {
// 		status = read_print(0,MMC_BASE_ADDR + DWMCI_CMD);
// 		if (timeout-- < 0) {
// 			print_uart("Timeout!\n");
// 			return -ETIMEDOUT;
// 		}
// 	} while (status & DWMCI_CMD_START);

// 	host->clock = freq;

// 	return 0;
// }

// #ifdef CONFIG_DM_MMC
// static int dwmci_set_ios(struct udevice *dev)
// {
// 	struct mmc *mmc = mmc_get_mmc_dev(dev);
// #else
// static int dwmci_set_ios(struct mmc *mmc)
// {
// #endif
// 	struct dwmci_host *host = (struct dwmci_host *)mmc->priv;
// 	u32_t ctype, regs;

// 	// print_uart("Buswidth = %d, clock: %d\n", mmc->bus_width, mmc->clock);

// 	dwmci_setup_bus(host, mmc->clock);
// 	switch (mmc->bus_width) {
// 	case 8:
// 		ctype = DWMCI_CTYPE_8BIT;
// 		break;
// 	case 4:
// 		ctype = DWMCI_CTYPE_4BIT;
// 		break;
// 	default:
// 		ctype = DWMCI_CTYPE_1BIT;
// 		break;
// 	}

// 	dwmci_write_print(0,host, DWMCI_CTYPE, ctype);

// 	regs = read_print(0,MMC_BASE_ADDR + DWMCI_UHS_REG);
// 	if (mmc->ddr_mode)
// 		regs |= DWMCI_DDR_MODE;
// 	else
// 		regs &= ~DWMCI_DDR_MODE;

// 	dwmci_write_print(0,host, DWMCI_UHS_REG, regs);

// 	if (host->clksel) {
// 		int ret;

// 		ret = host->clksel(host);
// 		if (ret)
// 			return ret;
// 	}

// #if CONFIG_IS_ENABLED(DM_REGULATOR)
// 	if (mmc->vqmmc_supply) {
// 		int ret;

// 		ret = regulator_set_enable_if_allowed(mmc->vqmmc_supply, false);
// 		if (ret)
// 			return ret;

// 		if (mmc->signal_voltage == MMC_SIGNAL_VOLTAGE_180)
// 			regulator_set_value(mmc->vqmmc_supply, 1800000);
// 		else
// 			regulator_set_value(mmc->vqmmc_supply, 3300000);

// 		ret = regulator_set_enable_if_allowed(mmc->vqmmc_supply, true);
// 		if (ret)
// 			return ret;
// 	}
// #endif

// 	return 0;
// }

// static int dwmci_init(struct mmc *mmc)
// {
// 	struct dwmci_host *host = mmc->priv;

// 	if (host->board_init)
// 		host->board_init(host);

// 	dwmci_write_print(0,host, DWMCI_PWREN, 1);

// 	if (!dwmci_wait_reset(host, DWMCI_RESET_ALL)) {
// 		print_uart(" Fail-reset!!\n");
// 		return -EIO;
// 	}

// 	/* Enumerate at 400KHz */
// 	dwmci_setup_bus(host, mmc->cfg->f_min);

// 	dwmci_write_print(0,host, DWMCI_RINTSTS, 0xFFFFFFFF);
// 	dwmci_write_print(0,host, DWMCI_INTMASK, 0);

// 	dwmci_write_print(0,host, DWMCI_TMOUT, 0xFFFFFFFF);

// 	dwmci_write_print(0,host, DWMCI_IDINTEN, 0);
// 	dwmci_write_print(0,host, DWMCI_BMOD, 1);

// 	if (!host->fifoth_val) {
// 		uint32_t fifo_size;

// 		fifo_size = read_print(0,MMC_BASE_ADDR + DWMCI_FIFOTH);
// 		fifo_size = ((fifo_size & RX_WMARK_MASK) >> RX_WMARK_SHIFT) + 1;
// 		host->fifoth_val = MSIZE(0x2) | RX_WMARK(fifo_size / 2 - 1) |
// 				TX_WMARK(fifo_size / 2);
// 	}
// 	dwmci_write_print(0,host, DWMCI_FIFOTH, host->fifoth_val);

// 	dwmci_write_print(0,host, DWMCI_CLKENA, 0);
// 	dwmci_write_print(0,host, DWMCI_CLKSRC, 0);

// 	if (!host->fifo_mode)
// 		dwmci_write_print(0,host, DWMCI_IDINTEN, DWMCI_IDINTEN_MASK);

// 	return 0;
// }

// #ifdef CONFIG_DM_MMC
// int dwmci_probe(struct udevice *dev)
// {
// 	struct mmc *mmc = mmc_get_mmc_dev(dev);

// 	return dwmci_init(mmc);
// }

// const struct dm_mmc_ops dm_dwmci_ops = {
// 	.send_cmd	= dwmci_send_cmd,
// 	.set_ios	= dwmci_set_ios,
// };

// #else
// static const struct mmc_ops dwmci_ops = {
// 	.send_cmd	= dwmci_send_cmd,
// 	.set_ios	= dwmci_set_ios,
// 	.init		= dwmci_init,
// };
// #endif

// void dwmci_setup_cfg(struct mmc_config *cfg, struct dwmci_host *host,
// 		u32_t max_clk, u32_t min_clk)
// {
// 	cfg->name = host->name;
// #ifndef CONFIG_DM_MMC
// 	cfg->ops = &dwmci_ops;
// #endif
// 	cfg->f_min = min_clk;
// 	cfg->f_max = max_clk;

// 	cfg->voltages = MMC_VDD_32_33 | MMC_VDD_33_34 | MMC_VDD_165_195;

// 	cfg->host_caps = host->caps;

// 	if (host->buswidth == 8) {
// 		cfg->host_caps |= MMC_MODE_8BIT;
// 		cfg->host_caps &= ~MMC_MODE_4BIT;
// 	} else {
// 		cfg->host_caps |= MMC_MODE_4BIT;
// 		cfg->host_caps &= ~MMC_MODE_8BIT;
// 	}
// 	cfg->host_caps |= MMC_MODE_HS | MMC_MODE_HS_52MHz;

// 	cfg->b_max = CONFIG_SYS_MMC_MAX_BLK_COUNT;
// }

// #ifdef CONFIG_BLK
// int dwmci_bind(struct udevice *dev, struct mmc *mmc, struct mmc_config *cfg)
// {
// 	return mmc_bind(dev, mmc, cfg);
// }
// #else
// int add_dwmci(struct dwmci_host *host, u32_t max_clk, u32_t min_clk)
// {
// 	dwmci_setup_cfg(&host->cfg, host, max_clk, min_clk);

// 	host->mmc = mmc_create(&host->cfg, host);
// 	if (host->mmc == NULL)
// 		return -1;

// 	return 0;
// }
// #endif

static void mmc_trace_before_send(const struct mmc_cmd *cmd)
{
	print_uart("CMD_SEND: 0x");
	print_uart_byte(cmd->cmdidx);
	print_uart("\r\n");
	print_uart("\t\tARG\t\t\t 0x");
	print_uart_int(cmd->cmdarg);
	print_uart("\r\n");
}


// static void mmc_trace_after_send(const struct mmc_cmd *cmd, u8_t ret)
// {}
static void mmc_trace_after_send(const struct mmc_cmd *cmd, u8_t ret)
{
	u8_t i;
	u8_t *ptr = NULL;

	if (ret)
	{
		print_uart("\t\tRET\t\t\t ");
		print_uart_byte(ret);
		print_uart("\r\n");
	}
	else
	{
		switch (cmd->resp_type)
		{
		case MMC_RSP_NONE:
			print_uart("\t\tMMC_RSP_NONE\r\n");
			break;
		case MMC_RSP_R1:
			print_uart("\t\tMMC_RSP_R1,5,6,7 \t 0x");
			print_uart_int(cmd->response[0]);
			print_uart("\r\n");
			break;
		case MMC_RSP_R1b:
			print_uart("\t\tMMC_RSP_R1b\t\t 0x");
			print_uart_int(cmd->response[0]);
			print_uart("\r\n");
			break;
		case MMC_RSP_R2:
			print_uart("\t\tMMC_RSP_R2\t\t 0x");
			print_uart_int(cmd->response[0]);
			print_uart("\r\n");
			print_uart("\t\t          \t\t 0x");
			print_uart_int(cmd->response[1]);
			print_uart("\r\n");
			print_uart("\t\t          \t\t 0x");
			print_uart_int(cmd->response[2]);
			print_uart("\r\n");
			print_uart("\t\t          \t\t 0x");
			print_uart_int(cmd->response[3]);
			print_uart("\r\n");

			print_uart("\r\n");
			print_uart("\t\t\t\t\tDUMPING DATA\r\n");
			for (i = 0; i < 4; i++)
			{
				u8_t j;
				print_uart("\t\t\t\t\t0x");
				print_uart_byte(i*4);
				print_uart (" - ");
				ptr = (u8_t *)&cmd->response[i];
				ptr += 3;
				for (j = 0; j < 4; j++)
				{
					print_uart_byte(*ptr--);
					print_uart(" ");
				}
				print_uart("\r\n");
			}
			break;
		case MMC_RSP_R3:
			print_uart("\t\tMMC_RSP_R3,4\t\t 0x");
			print_uart_int(cmd->response[0]);
			print_uart("\r\n");
			break;
		default:
			print_uart("\t\tERROR MMC rsp not supported\r\n");
			break;
		}
	}
}


// Send cmd0
u8_t mmc_go_idle( volatile struct sdhci_host_t *g_dwc_mshc)
{
	struct mmc_cmd cmd0 = {0};
	u8_t err = 0;
	// if (!dwmci_wait_reset(DWMCI_CTRL_DMA_RESET)) {
	// 	print_uart(" Fail-reset!!\n");
	// 	return -EIO;
	// }
	udelay(1000);

	cmd0.cmdidx = MMC_CMD_GO_IDLE_STATE;
	cmd0.cmdarg = 0;
	cmd0.resp_type = MMC_RSP_NONE;

	mmc_trace_before_send(&cmd0);
	err = dwmci_send_cmd(&cmd0, NULL);
	mmc_trace_after_send(&cmd0, err);

	if (err)
		return err;

	udelay(2000);

	return err;
}


// Send Interface Condition Command (CMD8). Same function for mmc and sd cards
u8_t mmc_send_if_cond(volatile struct sdhci_host_t *g_dwc_mshc)
{
	struct mmc_cmd cmd8 = {0};
	u8_t err = 0;

	cmd8.cmdidx = SD_CMD_SEND_IF_COND;
	/* We set the bit if the host supports voltages between 2.7 and 3.6 V */
	cmd8.cmdarg = (((MMC_VDD_32_33 | MMC_VDD_33_34) & 0xff8000) != 0) << 8 | 0xaa;
	cmd8.resp_type = MMC_RSP_R7;

	mmc_trace_before_send(&cmd8);
	err = dwmci_send_cmd(&cmd8, NULL);
	mmc_trace_after_send(&cmd8, err);

	return err;
}


// Send Operating Condition Command (ACMD41). SD specific.
u8_t sd_send_op_cond(volatile struct sdhci_host_t *g_dwc_mshc)
{
	u32_t timeout = 1000;
	u8_t err = 0;
	struct mmc_cmd acmd41 = {0};

	while (1)
	{
		// we send cmd55 first
		acmd41.cmdidx = MMC_CMD_APP_CMD;
		acmd41.resp_type = MMC_RSP_R1;
		acmd41.cmdarg = 0;

		mmc_trace_before_send(&acmd41);
		err = dwmci_send_cmd(&acmd41, NULL);
		mmc_trace_after_send(&acmd41, err);

		if (err)
			return err;

		// we then send acmd41
		acmd41.cmdidx = SD_CMD_APP_SEND_OP_COND;
		acmd41.resp_type = MMC_RSP_R3;

		/*
		 * Most cards do not answer if some reserved bits
		 * in the ocr are set. However, Some controller
		 * can set bit 7 (reserved for low voltages), but
		 * how to manage low voltages SD card is not yet
		 * specified.
		 */
		acmd41.cmdarg = (MMC_VDD_32_33 | MMC_VDD_33_34) & 0xff8000;

		// if (g_dwc_mshc->card_version == SD_VERSION_2)
			acmd41.cmdarg |= OCR_HCS;

		mmc_trace_before_send(&acmd41);
		err = dwmci_send_cmd(&acmd41, NULL);
		mmc_trace_after_send(&acmd41, err);

		if (err)
			return err;

		// This bit is set to LOW if the card has not finished the power up routine.
		if (acmd41.response[0] & OCR_BUSY)
			break;

		if (timeout-- <= 0)
			return EOPNOTSUPP;

		udelay(1000);
	}

	return err;
}



// Send CMD2 ALL_SEND_CID
u8_t mmc_send_cid(volatile struct sdhci_host_t *g_dwc_mshc)
{
	u8_t err = 0;
	struct mmc_cmd cmd2 = {0};

	cmd2.cmdidx = MMC_CMD_ALL_SEND_CID;
	cmd2.resp_type = MMC_RSP_R2;
	cmd2.cmdarg = 0;

	mmc_trace_before_send(&cmd2);
	err = dwmci_send_cmd(&cmd2, NULL);
	mmc_trace_after_send(&cmd2, err);
	
	return err;
}


// Send CMD3 SD_CMD_SEND_RELATIVE_ADDR
u8_t sd_send_rca(volatile struct sdhci_host_t *g_dwc_mshc)
{
	u8_t err = 0;
	struct mmc_cmd cmd3 = {0};

	cmd3.cmdidx = SD_CMD_SEND_RELATIVE_ADDR;
	cmd3.resp_type = MMC_RSP_R6;
	cmd3.cmdarg = g_dwc_mshc->rca << 16;

	mmc_trace_before_send(&cmd3);
	err = dwmci_send_cmd(&cmd3, NULL);
	mmc_trace_after_send(&cmd3, err);

	if (err)
		return err;

	g_dwc_mshc->rca = (cmd3.response[0] >> 16) & 0xffff;

	return err;
}


// Send CMD7 MMC_CMD_SELECT_CARD
u8_t sd_select_card(volatile struct sdhci_host_t *g_dwc_mshc)
{
	u8_t err = 0;
	struct mmc_cmd cmd7 = {0};

	/* Select the card, and put it into Transfer Mode */
	cmd7.cmdidx = MMC_CMD_SELECT_CARD;
	cmd7.resp_type = MMC_RSP_R1;
	cmd7.cmdarg = g_dwc_mshc->rca << 16;

	mmc_trace_before_send(&cmd7);
	err = dwmci_send_cmd(&cmd7, NULL);
	mmc_trace_after_send(&cmd7, err);

	return err;
}


// Send CMD9 MMC_CMD_SEND_CSD
u8_t sd_send_csd(volatile struct sdhci_host_t *g_dwc_mshc)
{
	u8_t err = 0;
	struct mmc_cmd cmd9 = {0};


	/* Get the Card-Specific Data */
	cmd9.cmdidx = MMC_CMD_SEND_CSD;
	cmd9.resp_type = MMC_RSP_R2;
	cmd9.cmdarg = g_dwc_mshc->rca << 16;

	mmc_trace_before_send(&cmd9);
	err = dwmci_send_cmd(&cmd9, NULL);
	mmc_trace_after_send(&cmd9, err);

	return err;
}


// Send ACMD51 SD_CMD_APP_SEND_SCR
u8_t sd_send_scr(volatile struct sdhci_host_t *g_dwc_mshc)
{
	u8_t err = 0;

	struct mmc_cmd acmd51;
	struct mmc_data data;

	// ALLOC_CACHE_ALIGN_BUFFER(u32_t,scr,2);
	u32_t *scr = (u32_t *) (0xFFE20000);

	// u32_t scr[2];

	/* Read the SCR to find out if this card supports higher speeds */
	acmd51.cmdidx = MMC_CMD_APP_CMD;
	acmd51.resp_type = MMC_RSP_R1;
	acmd51.cmdarg = g_dwc_mshc->rca << 16;

	mmc_trace_before_send(&acmd51);
	err = dwmci_send_cmd(&acmd51, NULL);
	mmc_trace_after_send(&acmd51, err);

	if (err)
		return err;


	acmd51.cmdidx = SD_CMD_APP_SEND_SCR;
	acmd51.resp_type = MMC_RSP_R1;
	acmd51.cmdarg = 0;

	data.dest = (u8_t *)scr;
	data.blocksize = 8; // SCR 64bits
	data.blocks = 1;
	data.flags = MMC_DATA_READ;

	mmc_trace_before_send(&acmd51);
	err = dwmci_send_cmd(&acmd51, &data);
	mmc_trace_after_send(&acmd51, err);

	return err;

}

// Send CMD16 MMC_CMD_SET_BLOCKLEN
u8_t mmc_set_blocklen(volatile struct sdhci_host_t *g_dwc_mshc, u32_t len)
{
	u8_t err = 0;
	struct mmc_cmd cmd16;

	cmd16.cmdidx = MMC_CMD_SET_BLOCKLEN;
	cmd16.resp_type = MMC_RSP_R1;
	cmd16.cmdarg = len;

	mmc_trace_before_send(&cmd16);
	err = dwmci_send_cmd(&cmd16, NULL);
	mmc_trace_after_send(&cmd16, err);

	return err;
}

// Set the number of block to read from the SD card.
static u8_t set_block_count(u32_t blkcnt)
{
	u8_t err = 0;
	struct mmc_cmd cmd23;

	cmd23.cmdidx = MMC_CMD_SET_BLOCK_COUNT;
	cmd23.cmdarg = blkcnt;
	cmd23.resp_type = MMC_RSP_R1;

	// mmc_trace_before_send(&cmd23);
	err = dwmci_send_cmd(&cmd23, NULL);
	// mmc_trace_after_send(&cmd23, err);	

	return err;
}

// struct spl_image_info {
// 	const char *name;
// 	u8_t os;
// 	uintptr_t load_addr;
// 	uintptr_t entry_point;
// // #if CONFIG_IS_ENABLED(LOAD_FIT) || CONFIG_IS_ENABLED(LOAD_FIT_FULL)
// 	void *fdt_addr;
// // #endif
// 	u32_t boot_device;
// 	u32_t offset;
// 	u32_t size;
// 	u32_t flags;
// 	void *arg;
// // #ifdef CONFIG_SPL_LEGACY_IMAGE_CRC_CHECK
// 	unsigned long dcrc_data;
// 	unsigned long dcrc_length;
// 	unsigned long dcrc;
// // #endif
// };

// struct spl_load_info {
// 	void *priv;
// 	/**
// 	 * read() - Read from device
// 	 *
// 	 * @load: Information about the load state
// 	 * @offset: Offset to read from in bytes. This must be a multiple of
// 	 *          @load->bl_len.
// 	 * @count: Number of bytes to read. This must be a multiple of
// 	 *         @load->bl_len.
// 	 * @buf: Buffer to read into
// 	 * @return number of bytes read, 0 on error
// 	 */
// 	unsigned long (*read)(struct spl_load_info *load, unsigned long sector, unsigned long count,
// 		      void *buf);
// // #if IS_ENABLED(CONFIG_SPL_LOAD_BLOCK)
// 	int bl_len;
// };

// int fat_read_file(const char *filename, void *buf, off_t offset, off_t len,
// 		  off_t *actread)
// {
// 	fsdata fsdata;
// 	fat_itr *itr;
// 	int ret;

// 	itr = malloc_cache_aligned(sizeof(fat_itr));
// 	if (!itr)
// 		return -ENOMEM;
// 	ret = fat_itr_root(itr, &fsdata);
// 	if (ret)
// 		goto out_free_itr;

// 	ret = fat_itr_resolve(itr, filename, TYPE_FILE);
// 	if (ret)
// 		goto out_free_both;

// 	printf("reading %s at pos %llu\n", filename, offset);

// 	/* For saving default max clustersize memory allocated to malloc pool */
// 	dir_entry *dentptr = itr->dent;

// 	ret = get_contents(&fsdata, dentptr, offset, buf, len, actread);

// out_free_both:
// 	free(fsdata.fatbuf);
// out_free_itr:
// 	free(itr);
// 	return ret;
// }

// static unsigned long spl_fit_read(struct spl_load_info *load, unsigned long file_offset,
// 			  unsigned long size, void *buf)
// {
// 	off_t actread;
// 	int ret;
// 	char *filename = load->priv;

// 	ret = fat_read_file(filename, buf, file_offset, size, &actread);
// 	if (ret)
// 		return ret;

// 	return actread;
// }

// int spl_load_image_fat(struct blk_desc *block_dev, int partition,
// 		       const char *filename)
// {
// 	struct spl_image_info *spl_image;
// 	struct spl_boot_device *bootdev;
// 	int err;
// 	off_t size;
// 	struct spl_load_info load;
// 	printf("partition %x filename %s block_dev %x \n",partition,filename,block_dev);
// 	// err = spl_register_fat_device(block_dev, partition);
// 	// if (err)
// 	// 	goto end;

// 	/*
// 	 * Avoid pulling in this function for other image types since we are
// 	 * very short on space on some boards.
// 	 */
// 	// if (IS_ENABLED(CONFIG_SPL_LOAD_FIT_FULL)) {
// 	// 	printf("config spl load fit full \n");
// 	// 	err = fat_size(filename, &size);
// 	// 	if (err)
// 	// 		goto end;
// 	// } else {
// 		size = 0;
// 	// }

// 	load.read = spl_fit_read;
// 	// if (IS_ENABLED(CONFIG_SPL_FS_FAT_DMA_ALIGN)){
// 		printf("spl set bl len dma \n");
// 		spl_set_bl_len(&load, ARCH_DMA_MINALIGN);
// 	// else{
// 	// 	printf("spl set bl len 1 \n");
// 	// 	spl_set_bl_len(&load, 1);}
// 	load.priv = (void *)filename;
// 	printf("call to spl load \n");
// 	err = spl_load(spl_image, bootdev, &load, size, 0);

// end:
// // #ifdef CONFIG_SPL_LIBCOMMON_SUPPORT
// // 	if (err < 0)
// // 		printf("%s: error reading image %s, err - %d\n",
// // 		       __func__, filename, err);
// // #endif

// 	return err;
// }

// Copies the data blocks from the SD card to dst by sending the read command. The blkcnt argument type is u64_t because lbas are 64 bits integer in the gpt format. But the block size argument of the read command is a u32_t. Since blkcnt is the result of the subtraction between two lbas and given the size of the linux image, we assume blkcnt will NEVER be above the maximum value of a u32_t. We can then safely cast blkcnt from u64_t to u32_t.
u8_t sd_copy_mmc(void *dst, u64_t src_lba, u64_t blkcnt)
{
	u8_t err = 0;

	struct mmc_cmd cmd18;
	struct mmc_data data;

	if (blkcnt > 1)
	{
		err = set_block_count(blkcnt);
		if (err)
			return err;
		cmd18.cmdidx = MMC_CMD_READ_MULTIPLE_BLOCK;
	}
	else
		cmd18.cmdidx = MMC_CMD_READ_SINGLE_BLOCK;

	/*
	We assume the card is high capacity as all SD Card today are.
	The check of the SD card high capacity property is done during "Send Operating Condition Command (ACMD41)" in the OCR register.
	*/
	// if (g_dwc_mshc->high_capacity)
		cmd18.cmdarg = src_lba;
	// else
	// 	cmd18.cmdarg = src_lba * g_dwc_mshc->read_bl_len;

	cmd18.resp_type = MMC_RSP_R1;

	data.dest = dst;
	// The blkcnt argument type is u64_t because lbas are 64 bits integer in the gpt format. But the block size argument of the read command is a u32_t. Since blkcnt is the result of the subtraction between two lbas and given the size of the linux image, we assume blkcnt will NEVER be above the maximum value of a u32_t. We can then safely cast blkcnt from u64_t to u32_t.
	data.blocks = (u32_t) blkcnt;
	data.blocksize = 0x200; // blocksize is 512 by default
	data.flags = MMC_DATA_READ;

	// mmc_trace_before_send(&cmd18);
	err = dwmci_send_cmd(&cmd18, &data);
	// mmc_trace_after_send(&cmd18, err);	

	return err;
}

