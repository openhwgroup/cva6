
/* THIS FILE HAS BEEN GENERATED, DO NOT MODIFY IT.
 */

/*
 * Copyright (C) 2018 ETH Zurich, University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __INCLUDE_ARCHI_UDMA_I2S_UDMA_I2S_V2_H__
#define __INCLUDE_ARCHI_UDMA_I2S_UDMA_I2S_V2_H__

#ifndef LANGUAGE_ASSEMBLY

#include <stdint.h>
#include "archi/utils.h"

#endif




//
// REGISTERS
//

// RX Channel 0 I2S uDMA transfer address of associated buffer
#define UDMA_I2S_I2S_RX_SADDR_OFFSET             0x0

// RX Channel 0 I2S uDMA transfer size of buffer
#define UDMA_I2S_I2S_RX_SIZE_OFFSET              0x4

// RX Channel 0 I2S uDMA transfer configuration
#define UDMA_I2S_I2S_RX_CFG_OFFSET               0x8

// -
#define UDMA_I2S_I2S_RX_INITCFG_OFFSET           0xc

//  TX Channel I2S uDMA transfer address of associated buffer
#define UDMA_I2S_I2S_TX_SADDR_OFFSET             0x10

//  TX Channel I2S uDMA transfer size of buffer
#define UDMA_I2S_I2S_TX_SIZE_OFFSET              0x14

//  TX Channel I2S uDMA transfer configuration
#define UDMA_I2S_I2S_TX_CFG_OFFSET               0x18

// -
#define UDMA_I2S_I2S_TX_INITCFG_OFFSET           0x1c

// Clock configuration for both master, slave and pdm
#define UDMA_I2S_I2S_CLKCFG_SETUP_OFFSET         0x20

// Configuration of I2S slave
#define UDMA_I2S_I2S_SLV_SETUP_OFFSET            0x24

// Configuration of I2S master
#define UDMA_I2S_I2S_MST_SETUP_OFFSET            0x28

// Configuration of PDM module
#define UDMA_I2S_I2S_PDM_SETUP_OFFSET            0x2c

//Configuration of DSP mode for slave
#define UDMA_I2S_I2S_SLV_DSP_SETUP_OFFSET        0x30

//Configuration of DSP mode for MASTER
#define UDMA_I2S_I2S_MST_DSP_SETUP_OFFSET        0x34

//
// REGISTERS FIELDS
//

// Configure pointer to memory buffer: - Read: value of the pointer until transfer is over. Else returns 0 - Write: set Address Pointer to memory buffer start address (access: R/W)
#define UDMA_I2S_I2S_RX_SADDR_RX_SADDR_BIT                           0
#define UDMA_I2S_I2S_RX_SADDR_RX_SADDR_WIDTH                         16
#define UDMA_I2S_I2S_RX_SADDR_RX_SADDR_MASK                          0xffff

// Buffer size in byte. (128kBytes maximum) - Read: buffer size left - Write: set buffer size (access: R/W)
#define UDMA_I2S_I2S_RX_SIZE_RX_SIZE_BIT                             0
#define UDMA_I2S_I2S_RX_SIZE_RX_SIZE_WIDTH                           17
#define UDMA_I2S_I2S_RX_SIZE_RX_SIZE_MASK                            0x1ffff

// Channel continuous mode: -1'b0: disable -1'b1: enable At the end of the buffer the uDMA reloads the address and size and starts a new transfer. (access: R/W)
#define UDMA_I2S_I2S_RX_CFG_CONTINOUS_BIT                            0
#define UDMA_I2S_I2S_RX_CFG_CONTINOUS_WIDTH                          1
#define UDMA_I2S_I2S_RX_CFG_CONTINOUS_MASK                           0x1

// Channel transfer size used to increment uDMA buffer address pointer: - 2'b00: +1 (8 bits) - 2'b01: +2 (16 bits) - 2'b10: +4 (32 bits) - 2'b11: +0 (access: R/W)
#define UDMA_I2S_I2S_RX_CFG_DATASIZE_BIT                             1
#define UDMA_I2S_I2S_RX_CFG_DATASIZE_WIDTH                           2
#define UDMA_I2S_I2S_RX_CFG_DATASIZE_MASK                            0x6

// Channel enable and start transfer: -1'b0: disable -1'b1: enable This signal is used also to queue a transfer if one is already ongoing. (access: R/W)
#define UDMA_I2S_I2S_RX_CFG_EN_BIT                                   4
#define UDMA_I2S_I2S_RX_CFG_EN_WIDTH                                 1
#define UDMA_I2S_I2S_RX_CFG_EN_MASK                                  0x10

// Channel clear and stop transfer: -1'b0: disable -1'b1: enable (access: W)
#define UDMA_I2S_I2S_RX_CFG_CLR_BIT                                  5
#define UDMA_I2S_I2S_RX_CFG_CLR_WIDTH                                1
#define UDMA_I2S_I2S_RX_CFG_CLR_MASK                                 0x20

// Transfer pending in queue status flag: -1'b0: free -1'b1: pending (access: R)
#define UDMA_I2S_I2S_RX_CFG_PENDING_BIT                              5
#define UDMA_I2S_I2S_RX_CFG_PENDING_WIDTH                            1
#define UDMA_I2S_I2S_RX_CFG_PENDING_MASK                             0x20

// Configure pointer to memory buffer: - Read: value of the pointer until transfer is over. Else returns 0 - Write: set Address Pointer to memory buffer start address (access: R/W)
#define UDMA_I2S_I2S_TX_SADDR_TX_SADDR_BIT                           0
#define UDMA_I2S_I2S_TX_SADDR_TX_SADDR_WIDTH                         16
#define UDMA_I2S_I2S_TX_SADDR_TX_SADDR_MASK                          0xffff

// Buffer size in byte. (128kBytes maximum) - Read: buffer size left - Write: set buffer size (access: R/W)
#define UDMA_I2S_I2S_TX_SIZE_TX_SIZE_BIT                             0
#define UDMA_I2S_I2S_TX_SIZE_TX_SIZE_WIDTH                           17
#define UDMA_I2S_I2S_TX_SIZE_TX_SIZE_MASK                            0x1ffff

// Channel continuous mode: -1'b0: disable -1'b1: enable At the end of the buffer the uDMA reloads the address and size and starts a new transfer. (access: R/W)
#define UDMA_I2S_I2S_TX_CFG_CONTINOUS_BIT                            0
#define UDMA_I2S_I2S_TX_CFG_CONTINOUS_WIDTH                          1
#define UDMA_I2S_I2S_TX_CFG_CONTINOUS_MASK                           0x1

// Channel transfer size used to increment uDMA buffer address pointer: - 2'b00: +1 (8 bits) - 2'b01: +2 (16 bits) - 2'b10: +4 (32 bits) - 2'b11: +0 (access: R/W)
#define UDMA_I2S_I2S_TX_CFG_DATASIZE_BIT                             1
#define UDMA_I2S_I2S_TX_CFG_DATASIZE_WIDTH                           2
#define UDMA_I2S_I2S_TX_CFG_DATASIZE_MASK                            0x6

// Channel enable and start transfer: -1'b0: disable -1'b1: enable This signal is used also to queue a transfer if one is already ongoing. (access: R/W)
#define UDMA_I2S_I2S_TX_CFG_EN_BIT                                   4
#define UDMA_I2S_I2S_TX_CFG_EN_WIDTH                                 1
#define UDMA_I2S_I2S_TX_CFG_EN_MASK                                  0x10

// Channel clear and stop transfer: -1'b0: disable -1'b1: enable (access: R/W)
#define UDMA_I2S_I2S_TX_CFG_CLR_BIT                                  5
#define UDMA_I2S_I2S_TX_CFG_CLR_WIDTH                                1
#define UDMA_I2S_I2S_TX_CFG_CLR_MASK                                 0x20

// Transfer pending in queue status flag: -1'b0: free -1'b1: pending (access: R)
#define UDMA_I2S_I2S_TX_CFG_PENDING_BIT                              5
#define UDMA_I2S_I2S_TX_CFG_PENDING_WIDTH                            1
#define UDMA_I2S_I2S_TX_CFG_PENDING_MASK                             0x20

// LSB of master clock divider (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_BIT                 0
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_WIDTH               8
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_MASK                0xff

// LSB of slave clock divider (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_BIT                  8
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_WIDTH                8
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_MASK                 0xff00

// MSBs of both master and slave clock divider (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_BIT                 16
#define UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_WIDTH               8
#define UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_MASK                0xff0000

// Enables Slave clock (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_BIT                   24
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_WIDTH                 1
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_MASK                  0x1000000

// Enables Master clock (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_BIT                  25
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_WIDTH                1
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_MASK                 0x2000000

// When enabled slave output clock is taken from PDM module (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_BIT                     26
#define UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_WIDTH                   1
#define UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_MASK                    0x4000000

// When set uses external clock for slave (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_BIT                      28
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_WIDTH                    1
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_MASK                     0x10000000

// Selects slave clock source(either ext or generated): -1’b0:selects master -1’b1:selects slave (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_BIT                      29
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_WIDTH                    1
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_MASK                     0x20000000

// When set uses external clock for master (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_BIT                     30
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_WIDTH                   1
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_MASK                    0x40000000

// Selects master clock source(either ext or generated): -1’b0:selects master -1’b1:selects slave (access: R/W)
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_BIT                     31
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_WIDTH                   1
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_MASK                    0x80000000

// Sets how many words for each I2S phase (access: R/W)
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_BIT                       0
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_WIDTH                     3
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_MASK                      0x7

// Sets how many bits per word (access: R/W)
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_BIT                        8
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_WIDTH                      5
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_MASK                       0x1f00

// Enables LSB shifting (access: R/W)
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_BIT                         16
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_WIDTH                       1
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_MASK                        0x10000

// Enables both channels (access: R/W)
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_BIT                         17
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_WIDTH                       1
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_MASK                        0x20000

// Enables the Slave (access: R/W)
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_BIT                          31
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_WIDTH                        1
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_MASK                         0x80000000

// Sets how many words for each I2S phase (access: R/W)
#define UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_BIT                      0
#define UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_WIDTH                    3
#define UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_MASK                     0x7

// Sets how many bits per word (access: R/W)
#define UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_BIT                       8
#define UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_WIDTH                     5
#define UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_MASK                      0x1f00

// Enables LSB shifting (access: R/W)
#define UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_BIT                        16
#define UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_WIDTH                      1
#define UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_MASK                       0x10000

// Enables both channels (access: R/W)
#define UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_BIT                        17
#define UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_WIDTH                      1
#define UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_MASK                       0x20000

// Enables the Master (access: R/W)
#define UDMA_I2S_I2S_MST_SETUP_MASTER_EN_BIT                         31
#define UDMA_I2S_I2S_MST_SETUP_MASTER_EN_WIDTH                       1
#define UDMA_I2S_I2S_MST_SETUP_MASTER_EN_MASK                        0x80000000

// Shifts the output of the filter (access: R/W)
#define UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_BIT                         0
#define UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_WIDTH                       3
#define UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_MASK                        0x7

// Sets the decimation ratio of the filter (access: R/W)
#define UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_BIT                    3
#define UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_WIDTH                  10
#define UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_MASK                   0x1ff8

// nan (access: R/W)
#define UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_BIT                          13
#define UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_WIDTH                        2
#define UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_MASK                         0x6000

// nan (access: R/W)
#define UDMA_I2S_I2S_PDM_SETUP_PDM_EN_BIT                            31
#define UDMA_I2S_I2S_PDM_SETUP_PDM_EN_WIDTH                          1
#define UDMA_I2S_I2S_PDM_SETUP_PDM_EN_MASK                           0x80000000

//DSP slave setup
#define UDMA_I2S_I2S_SLV_DSP_SETUP_DSP_EN_BIT                        31
#define UDMA_I2S_I2S_SLV_DSP_SETUP_DSP_OFFSET_BIT                    20
#define UDMA_I2S_I2S_SLV_DSP_SETUP_DSP_MODE_BIT                      16
#define UDMA_I2S_I2S_SLV_DSP_SETUP_DSP_SETUP_TIME_BIT                0

//DSP master setup
#define UDMA_I2S_I2S_MST_DSP_SETUP_DSP_EN_BIT                        31
#define UDMA_I2S_I2S_MST_DSP_SETUP_DSP_OFFSET_BIT                    20
#define UDMA_I2S_I2S_MST_DSP_SETUP_DSP_MODE_BIT                      16
#define UDMA_I2S_I2S_MST_DSP_SETUP_DSP_SETUP_TIME_BIT                0

//
// REGISTERS STRUCTS
//

#ifndef LANGUAGE_ASSEMBLY

typedef union {
  struct {
    unsigned int rx_saddr        :16; // Configure pointer to memory buffer: - Read: value of the pointer until transfer is over. Else returns 0 - Write: set Address Pointer to memory buffer start address
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_rx_saddr_t;

typedef union {
  struct {
    unsigned int rx_size         :17; // Buffer size in byte. (128kBytes maximum) - Read: buffer size left - Write: set buffer size
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_rx_size_t;

typedef union {
  struct {
    unsigned int continous       :1 ; // Channel continuous mode: -1'b0: disable -1'b1: enable At the end of the buffer the uDMA reloads the address and size and starts a new transfer.
    unsigned int datasize        :2 ; // Channel transfer size used to increment uDMA buffer address pointer: - 2'b00: +1 (8 bits) - 2'b01: +2 (16 bits) - 2'b10: +4 (32 bits) - 2'b11: +0
    unsigned int padding0:1 ;
    unsigned int en              :1 ; // Channel enable and start transfer: -1'b0: disable -1'b1: enable This signal is used also to queue a transfer if one is already ongoing.
    unsigned int clr             :1 ; // Channel clear and stop transfer: -1'b0: disable -1'b1: enable
    unsigned int pending         :1 ; // Transfer pending in queue status flag: -1'b0: free -1'b1: pending
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_rx_cfg_t;

typedef union {
  struct {
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_rx_initcfg_t;

typedef union {
  struct {
    unsigned int tx_saddr        :16; // Configure pointer to memory buffer: - Read: value of the pointer until transfer is over. Else returns 0 - Write: set Address Pointer to memory buffer start address
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_tx_saddr_t;

typedef union {
  struct {
    unsigned int tx_size         :17; // Buffer size in byte. (128kBytes maximum) - Read: buffer size left - Write: set buffer size
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_tx_size_t;

typedef union {
  struct {
    unsigned int continous       :1 ; // Channel continuous mode: -1'b0: disable -1'b1: enable At the end of the buffer the uDMA reloads the address and size and starts a new transfer.
    unsigned int datasize        :2 ; // Channel transfer size used to increment uDMA buffer address pointer: - 2'b00: +1 (8 bits) - 2'b01: +2 (16 bits) - 2'b10: +4 (32 bits) - 2'b11: +0
    unsigned int padding0:1 ;
    unsigned int en              :1 ; // Channel enable and start transfer: -1'b0: disable -1'b1: enable This signal is used also to queue a transfer if one is already ongoing.
    unsigned int clr             :1 ; // Channel clear and stop transfer: -1'b0: disable -1'b1: enable
    unsigned int pending         :1 ; // Transfer pending in queue status flag: -1'b0: free -1'b1: pending
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_tx_cfg_t;

typedef union {
  struct {
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_tx_initcfg_t;

typedef union {
  struct {
    unsigned int master_clk_div  :8 ; // LSB of master clock divider
    unsigned int slave_clk_div   :8 ; // LSB of slave clock divider
    unsigned int common_clk_div  :8 ; // MSBs of both master and slave clock divider
    unsigned int slave_clk_en    :1 ; // Enables Slave clock
    unsigned int master_clk_en   :1 ; // Enables Master clock
    unsigned int pdm_clk_en      :1 ; // When enabled slave output clock is taken from PDM module
    unsigned int padding0:1 ;
    unsigned int slave_ext       :1 ; // When set uses external clock for slave
    unsigned int slave_num       :1 ; // Selects slave clock source(either ext or generated): -1’b0:selects master -1’b1:selects slave
    unsigned int master_ext      :1 ; // When set uses external clock for master
    unsigned int master_num      :1 ; // Selects master clock source(either ext or generated): -1’b0:selects master -1’b1:selects slave
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_clkcfg_setup_t;

typedef union {
  struct {
    unsigned int slave_words     :3 ; // Sets how many words for each I2S phase
    unsigned int padding0:5 ;
    unsigned int slave_bits      :5 ; // Sets how many bits per word
    unsigned int padding1:3 ;
    unsigned int slave_lsb       :1 ; // Enables LSB shifting
    unsigned int slave_2ch       :1 ; // Enables both channels
    unsigned int padding2:13;
    unsigned int slave_en        :1 ; // Enables the Slave
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_slv_setup_t;

typedef union {
  struct {
    unsigned int master_words    :3 ; // Sets how many words for each I2S phase
    unsigned int padding0:5 ;
    unsigned int master_bits     :5 ; // Sets how many bits per word
    unsigned int padding1:3 ;
    unsigned int master_lsb      :1 ; // Enables LSB shifting
    unsigned int master_2ch      :1 ; // Enables both channels
    unsigned int padding2:13;
    unsigned int master_en       :1 ; // Enables the Master
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_mst_setup_t;

typedef union {
  struct {
    unsigned int pdm_shift       :3 ; // Shifts the output of the filter
    unsigned int pdm_decimation  :10; // Sets the decimation ratio of the filter
    unsigned int pdm_mode        :2 ; // nan
    unsigned int padding0:16;
    unsigned int pdm_en          :1 ; // nan
  };
  unsigned int raw;
} __attribute__((packed)) udma_i2s_i2s_pdm_setup_t;

#endif



//
// REGISTERS STRUCTS
//

#ifdef __GVSOC__

class vp_udma_i2s_i2s_rx_saddr : public vp::reg_32
{
public:
  inline void rx_saddr_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_RX_SADDR_RX_SADDR_BIT, UDMA_I2S_I2S_RX_SADDR_RX_SADDR_WIDTH); }
  inline uint32_t rx_saddr_get() { return this->get_field(UDMA_I2S_I2S_RX_SADDR_RX_SADDR_BIT, UDMA_I2S_I2S_RX_SADDR_RX_SADDR_WIDTH); }
};

class vp_udma_i2s_i2s_rx_size : public vp::reg_32
{
public:
  inline void rx_size_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_RX_SIZE_RX_SIZE_BIT, UDMA_I2S_I2S_RX_SIZE_RX_SIZE_WIDTH); }
  inline uint32_t rx_size_get() { return this->get_field(UDMA_I2S_I2S_RX_SIZE_RX_SIZE_BIT, UDMA_I2S_I2S_RX_SIZE_RX_SIZE_WIDTH); }
};

class vp_udma_i2s_i2s_rx_cfg : public vp::reg_32
{
public:
  inline void continous_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_RX_CFG_CONTINOUS_BIT, UDMA_I2S_I2S_RX_CFG_CONTINOUS_WIDTH); }
  inline uint32_t continous_get() { return this->get_field(UDMA_I2S_I2S_RX_CFG_CONTINOUS_BIT, UDMA_I2S_I2S_RX_CFG_CONTINOUS_WIDTH); }
  inline void datasize_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_RX_CFG_DATASIZE_BIT, UDMA_I2S_I2S_RX_CFG_DATASIZE_WIDTH); }
  inline uint32_t datasize_get() { return this->get_field(UDMA_I2S_I2S_RX_CFG_DATASIZE_BIT, UDMA_I2S_I2S_RX_CFG_DATASIZE_WIDTH); }
  inline void en_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_RX_CFG_EN_BIT, UDMA_I2S_I2S_RX_CFG_EN_WIDTH); }
  inline uint32_t en_get() { return this->get_field(UDMA_I2S_I2S_RX_CFG_EN_BIT, UDMA_I2S_I2S_RX_CFG_EN_WIDTH); }
  inline void clr_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_RX_CFG_CLR_BIT, UDMA_I2S_I2S_RX_CFG_CLR_WIDTH); }
  inline uint32_t clr_get() { return this->get_field(UDMA_I2S_I2S_RX_CFG_CLR_BIT, UDMA_I2S_I2S_RX_CFG_CLR_WIDTH); }
  inline void pending_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_RX_CFG_PENDING_BIT, UDMA_I2S_I2S_RX_CFG_PENDING_WIDTH); }
  inline uint32_t pending_get() { return this->get_field(UDMA_I2S_I2S_RX_CFG_PENDING_BIT, UDMA_I2S_I2S_RX_CFG_PENDING_WIDTH); }
};

class vp_udma_i2s_i2s_tx_saddr : public vp::reg_32
{
public:
  inline void tx_saddr_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_TX_SADDR_TX_SADDR_BIT, UDMA_I2S_I2S_TX_SADDR_TX_SADDR_WIDTH); }
  inline uint32_t tx_saddr_get() { return this->get_field(UDMA_I2S_I2S_TX_SADDR_TX_SADDR_BIT, UDMA_I2S_I2S_TX_SADDR_TX_SADDR_WIDTH); }
};

class vp_udma_i2s_i2s_tx_size : public vp::reg_32
{
public:
  inline void tx_size_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_TX_SIZE_TX_SIZE_BIT, UDMA_I2S_I2S_TX_SIZE_TX_SIZE_WIDTH); }
  inline uint32_t tx_size_get() { return this->get_field(UDMA_I2S_I2S_TX_SIZE_TX_SIZE_BIT, UDMA_I2S_I2S_TX_SIZE_TX_SIZE_WIDTH); }
};

class vp_udma_i2s_i2s_tx_cfg : public vp::reg_32
{
public:
  inline void continous_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_TX_CFG_CONTINOUS_BIT, UDMA_I2S_I2S_TX_CFG_CONTINOUS_WIDTH); }
  inline uint32_t continous_get() { return this->get_field(UDMA_I2S_I2S_TX_CFG_CONTINOUS_BIT, UDMA_I2S_I2S_TX_CFG_CONTINOUS_WIDTH); }
  inline void datasize_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_TX_CFG_DATASIZE_BIT, UDMA_I2S_I2S_TX_CFG_DATASIZE_WIDTH); }
  inline uint32_t datasize_get() { return this->get_field(UDMA_I2S_I2S_TX_CFG_DATASIZE_BIT, UDMA_I2S_I2S_TX_CFG_DATASIZE_WIDTH); }
  inline void en_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_TX_CFG_EN_BIT, UDMA_I2S_I2S_TX_CFG_EN_WIDTH); }
  inline uint32_t en_get() { return this->get_field(UDMA_I2S_I2S_TX_CFG_EN_BIT, UDMA_I2S_I2S_TX_CFG_EN_WIDTH); }
  inline void clr_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_TX_CFG_CLR_BIT, UDMA_I2S_I2S_TX_CFG_CLR_WIDTH); }
  inline uint32_t clr_get() { return this->get_field(UDMA_I2S_I2S_TX_CFG_CLR_BIT, UDMA_I2S_I2S_TX_CFG_CLR_WIDTH); }
  inline void pending_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_TX_CFG_PENDING_BIT, UDMA_I2S_I2S_TX_CFG_PENDING_WIDTH); }
  inline uint32_t pending_get() { return this->get_field(UDMA_I2S_I2S_TX_CFG_PENDING_BIT, UDMA_I2S_I2S_TX_CFG_PENDING_WIDTH); }
};

class vp_udma_i2s_i2s_clkcfg_setup : public vp::reg_32
{
public:
  inline void master_clk_div_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_WIDTH); }
  inline uint32_t master_clk_div_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_WIDTH); }
  inline void slave_clk_div_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_WIDTH); }
  inline uint32_t slave_clk_div_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_WIDTH); }
  inline void common_clk_div_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_WIDTH); }
  inline uint32_t common_clk_div_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_WIDTH); }
  inline void slave_clk_en_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_WIDTH); }
  inline uint32_t slave_clk_en_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_WIDTH); }
  inline void master_clk_en_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_WIDTH); }
  inline uint32_t master_clk_en_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_WIDTH); }
  inline void pdm_clk_en_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_WIDTH); }
  inline uint32_t pdm_clk_en_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_WIDTH); }
  inline void slave_ext_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_WIDTH); }
  inline uint32_t slave_ext_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_WIDTH); }
  inline void slave_num_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_WIDTH); }
  inline uint32_t slave_num_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_WIDTH); }
  inline void master_ext_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_WIDTH); }
  inline uint32_t master_ext_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_WIDTH); }
  inline void master_num_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_WIDTH); }
  inline uint32_t master_num_get() { return this->get_field(UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_BIT, UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_WIDTH); }
};

class vp_udma_i2s_i2s_slv_setup : public vp::reg_32
{
public:
  inline void slave_words_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_WIDTH); }
  inline uint32_t slave_words_get() { return this->get_field(UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_WIDTH); }
  inline void slave_bits_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_WIDTH); }
  inline uint32_t slave_bits_get() { return this->get_field(UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_WIDTH); }
  inline void slave_lsb_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_WIDTH); }
  inline uint32_t slave_lsb_get() { return this->get_field(UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_WIDTH); }
  inline void slave_2ch_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_WIDTH); }
  inline uint32_t slave_2ch_get() { return this->get_field(UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_WIDTH); }
  inline void slave_en_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_WIDTH); }
  inline uint32_t slave_en_get() { return this->get_field(UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_BIT, UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_WIDTH); }
};

class vp_udma_i2s_i2s_mst_setup : public vp::reg_32
{
public:
  inline void master_words_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_WIDTH); }
  inline uint32_t master_words_get() { return this->get_field(UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_WIDTH); }
  inline void master_bits_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_WIDTH); }
  inline uint32_t master_bits_get() { return this->get_field(UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_WIDTH); }
  inline void master_lsb_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_WIDTH); }
  inline uint32_t master_lsb_get() { return this->get_field(UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_WIDTH); }
  inline void master_2ch_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_WIDTH); }
  inline uint32_t master_2ch_get() { return this->get_field(UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_WIDTH); }
  inline void master_en_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_MST_SETUP_MASTER_EN_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_EN_WIDTH); }
  inline uint32_t master_en_get() { return this->get_field(UDMA_I2S_I2S_MST_SETUP_MASTER_EN_BIT, UDMA_I2S_I2S_MST_SETUP_MASTER_EN_WIDTH); }
};

class vp_udma_i2s_i2s_pdm_setup : public vp::reg_32
{
public:
  inline void pdm_shift_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_BIT, UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_WIDTH); }
  inline uint32_t pdm_shift_get() { return this->get_field(UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_BIT, UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_WIDTH); }
  inline void pdm_decimation_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_BIT, UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_WIDTH); }
  inline uint32_t pdm_decimation_get() { return this->get_field(UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_BIT, UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_WIDTH); }
  inline void pdm_mode_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_BIT, UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_WIDTH); }
  inline uint32_t pdm_mode_get() { return this->get_field(UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_BIT, UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_WIDTH); }
  inline void pdm_en_set(uint32_t value) { this->set_field(value, UDMA_I2S_I2S_PDM_SETUP_PDM_EN_BIT, UDMA_I2S_I2S_PDM_SETUP_PDM_EN_WIDTH); }
  inline uint32_t pdm_en_get() { return this->get_field(UDMA_I2S_I2S_PDM_SETUP_PDM_EN_BIT, UDMA_I2S_I2S_PDM_SETUP_PDM_EN_WIDTH); }
};

#endif



//
// REGISTERS GLOBAL STRUCT
//

#ifndef LANGUAGE_ASSEMBLY

typedef struct {
  unsigned int i2s_rx_saddr    ; // RX Channel 0 I2S uDMA transfer address of associated buffer
  unsigned int i2s_rx_size     ; // RX Channel 0 I2S uDMA transfer size of buffer
  unsigned int i2s_rx_cfg      ; // RX Channel 0 I2S uDMA transfer configuration
  unsigned int i2s_rx_initcfg  ; // -
  unsigned int i2s_tx_saddr    ; //  TX Channel I2S uDMA transfer address of associated buffer
  unsigned int i2s_tx_size     ; //  TX Channel I2S uDMA transfer size of buffer
  unsigned int i2s_tx_cfg      ; //  TX Channel I2S uDMA transfer configuration
  unsigned int i2s_tx_initcfg  ; // -
  unsigned int i2s_clkcfg_setup; // Clock configuration for both master, slave and pdm
  unsigned int i2s_slv_setup   ; // Configuration of I2S slave
  unsigned int i2s_mst_setup   ; // Configuration of I2S master
  unsigned int i2s_pdm_setup   ; // Configuration of PDM module
} __attribute__((packed)) udma_i2s_udma_i2s_t;

#endif



//
// REGISTERS ACCESS FUNCTIONS
//

#ifndef LANGUAGE_ASSEMBLY

static inline uint32_t udma_i2s_i2s_rx_saddr_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_RX_SADDR_OFFSET); }
static inline void udma_i2s_i2s_rx_saddr_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_RX_SADDR_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_rx_size_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_RX_SIZE_OFFSET); }
static inline void udma_i2s_i2s_rx_size_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_RX_SIZE_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_rx_cfg_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_RX_CFG_OFFSET); }
static inline void udma_i2s_i2s_rx_cfg_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_RX_CFG_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_rx_initcfg_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_RX_INITCFG_OFFSET); }
static inline void udma_i2s_i2s_rx_initcfg_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_RX_INITCFG_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_tx_saddr_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_TX_SADDR_OFFSET); }
static inline void udma_i2s_i2s_tx_saddr_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_TX_SADDR_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_tx_size_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_TX_SIZE_OFFSET); }
static inline void udma_i2s_i2s_tx_size_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_TX_SIZE_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_tx_cfg_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_TX_CFG_OFFSET); }
static inline void udma_i2s_i2s_tx_cfg_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_TX_CFG_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_tx_initcfg_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_TX_INITCFG_OFFSET); }
static inline void udma_i2s_i2s_tx_initcfg_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_TX_INITCFG_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_clkcfg_setup_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_CLKCFG_SETUP_OFFSET); }
static inline void udma_i2s_i2s_clkcfg_setup_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_CLKCFG_SETUP_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_slv_setup_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_SLV_SETUP_OFFSET); }
static inline void udma_i2s_i2s_slv_setup_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_SLV_SETUP_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_mst_setup_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_MST_SETUP_OFFSET); }
static inline void udma_i2s_i2s_mst_setup_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_MST_SETUP_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_pdm_setup_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_PDM_SETUP_OFFSET); }
static inline void udma_i2s_i2s_pdm_setup_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_PDM_SETUP_OFFSET, value); }

//DSP functions
static inline uint32_t udma_i2s_i2s_slv_dsp_setup_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_SLV_DSP_SETUP_OFFSET); }
static inline void udma_i2s_i2s_slv_dsp_setup_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_SLV_DSP_SETUP_OFFSET, value); }

static inline uint32_t udma_i2s_i2s_mst_dsp_setup_get(uint32_t base) { return ARCHI_READ(base, UDMA_I2S_I2S_MST_DSP_SETUP_OFFSET); }
static inline void udma_i2s_i2s_mst_dsp_setup_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_I2S_I2S_MST_DSP_SETUP_OFFSET, value); }

#endif



//
// REGISTERS FIELDS MACROS
//

#ifndef LANGUAGE_ASSEMBLY

#define UDMA_I2S_I2S_RX_SADDR_RX_SADDR_GET(value)          (ARCHI_BEXTRACTU((value),16,0))
#define UDMA_I2S_I2S_RX_SADDR_RX_SADDR_GETS(value)         (ARCHI_BEXTRACT((value),16,0))
#define UDMA_I2S_I2S_RX_SADDR_RX_SADDR_SET(value,field)    (ARCHI_BINSERT((value),(field),16,0))
#define UDMA_I2S_I2S_RX_SADDR_RX_SADDR(val)                ((val) << 0)

#define UDMA_I2S_I2S_RX_SIZE_RX_SIZE_GET(value)            (ARCHI_BEXTRACTU((value),17,0))
#define UDMA_I2S_I2S_RX_SIZE_RX_SIZE_GETS(value)           (ARCHI_BEXTRACT((value),17,0))
#define UDMA_I2S_I2S_RX_SIZE_RX_SIZE_SET(value,field)      (ARCHI_BINSERT((value),(field),17,0))
#define UDMA_I2S_I2S_RX_SIZE_RX_SIZE(val)                  ((val) << 0)

#define UDMA_I2S_I2S_RX_CFG_CONTINOUS_GET(value)           (ARCHI_BEXTRACTU((value),1,0))
#define UDMA_I2S_I2S_RX_CFG_CONTINOUS_GETS(value)          (ARCHI_BEXTRACT((value),1,0))
#define UDMA_I2S_I2S_RX_CFG_CONTINOUS_SET(value,field)     (ARCHI_BINSERT((value),(field),1,0))
#define UDMA_I2S_I2S_RX_CFG_CONTINOUS(val)                 ((val) << 0)

#define UDMA_I2S_I2S_RX_CFG_DATASIZE_GET(value)            (ARCHI_BEXTRACTU((value),2,1))
#define UDMA_I2S_I2S_RX_CFG_DATASIZE_GETS(value)           (ARCHI_BEXTRACT((value),2,1))
#define UDMA_I2S_I2S_RX_CFG_DATASIZE_SET(value,field)      (ARCHI_BINSERT((value),(field),2,1))
#define UDMA_I2S_I2S_RX_CFG_DATASIZE(val)                  ((val) << 1)

#define UDMA_I2S_I2S_RX_CFG_EN_GET(value)                  (ARCHI_BEXTRACTU((value),1,4))
#define UDMA_I2S_I2S_RX_CFG_EN_GETS(value)                 (ARCHI_BEXTRACT((value),1,4))
#define UDMA_I2S_I2S_RX_CFG_EN_SET(value,field)            (ARCHI_BINSERT((value),(field),1,4))
#define UDMA_I2S_I2S_RX_CFG_EN(val)                        ((val) << 4)

#define UDMA_I2S_I2S_RX_CFG_CLR_GET(value)                 (ARCHI_BEXTRACTU((value),1,5))
#define UDMA_I2S_I2S_RX_CFG_CLR_GETS(value)                (ARCHI_BEXTRACT((value),1,5))
#define UDMA_I2S_I2S_RX_CFG_CLR_SET(value,field)           (ARCHI_BINSERT((value),(field),1,5))
#define UDMA_I2S_I2S_RX_CFG_CLR(val)                       ((val) << 5)

#define UDMA_I2S_I2S_RX_CFG_PENDING_GET(value)             (ARCHI_BEXTRACTU((value),1,5))
#define UDMA_I2S_I2S_RX_CFG_PENDING_GETS(value)            (ARCHI_BEXTRACT((value),1,5))
#define UDMA_I2S_I2S_RX_CFG_PENDING_SET(value,field)       (ARCHI_BINSERT((value),(field),1,5))
#define UDMA_I2S_I2S_RX_CFG_PENDING(val)                   ((val) << 5)

#define UDMA_I2S_I2S_TX_SADDR_TX_SADDR_GET(value)          (ARCHI_BEXTRACTU((value),16,0))
#define UDMA_I2S_I2S_TX_SADDR_TX_SADDR_GETS(value)         (ARCHI_BEXTRACT((value),16,0))
#define UDMA_I2S_I2S_TX_SADDR_TX_SADDR_SET(value,field)    (ARCHI_BINSERT((value),(field),16,0))
#define UDMA_I2S_I2S_TX_SADDR_TX_SADDR(val)                ((val) << 0)

#define UDMA_I2S_I2S_TX_SIZE_TX_SIZE_GET(value)            (ARCHI_BEXTRACTU((value),17,0))
#define UDMA_I2S_I2S_TX_SIZE_TX_SIZE_GETS(value)           (ARCHI_BEXTRACT((value),17,0))
#define UDMA_I2S_I2S_TX_SIZE_TX_SIZE_SET(value,field)      (ARCHI_BINSERT((value),(field),17,0))
#define UDMA_I2S_I2S_TX_SIZE_TX_SIZE(val)                  ((val) << 0)

#define UDMA_I2S_I2S_TX_CFG_CONTINOUS_GET(value)           (ARCHI_BEXTRACTU((value),1,0))
#define UDMA_I2S_I2S_TX_CFG_CONTINOUS_GETS(value)          (ARCHI_BEXTRACT((value),1,0))
#define UDMA_I2S_I2S_TX_CFG_CONTINOUS_SET(value,field)     (ARCHI_BINSERT((value),(field),1,0))
#define UDMA_I2S_I2S_TX_CFG_CONTINOUS(val)                 ((val) << 0)

#define UDMA_I2S_I2S_TX_CFG_DATASIZE_GET(value)            (ARCHI_BEXTRACTU((value),2,1))
#define UDMA_I2S_I2S_TX_CFG_DATASIZE_GETS(value)           (ARCHI_BEXTRACT((value),2,1))
#define UDMA_I2S_I2S_TX_CFG_DATASIZE_SET(value,field)      (ARCHI_BINSERT((value),(field),2,1))
#define UDMA_I2S_I2S_TX_CFG_DATASIZE(val)                  ((val) << 1)

#define UDMA_I2S_I2S_TX_CFG_EN_GET(value)                  (ARCHI_BEXTRACTU((value),1,4))
#define UDMA_I2S_I2S_TX_CFG_EN_GETS(value)                 (ARCHI_BEXTRACT((value),1,4))
#define UDMA_I2S_I2S_TX_CFG_EN_SET(value,field)            (ARCHI_BINSERT((value),(field),1,4))
#define UDMA_I2S_I2S_TX_CFG_EN(val)                        ((val) << 4)

#define UDMA_I2S_I2S_TX_CFG_CLR_GET(value)                 (ARCHI_BEXTRACTU((value),1,5))
#define UDMA_I2S_I2S_TX_CFG_CLR_GETS(value)                (ARCHI_BEXTRACT((value),1,5))
#define UDMA_I2S_I2S_TX_CFG_CLR_SET(value,field)           (ARCHI_BINSERT((value),(field),1,5))
#define UDMA_I2S_I2S_TX_CFG_CLR(val)                       ((val) << 5)

#define UDMA_I2S_I2S_TX_CFG_PENDING_GET(value)             (ARCHI_BEXTRACTU((value),1,5))
#define UDMA_I2S_I2S_TX_CFG_PENDING_GETS(value)            (ARCHI_BEXTRACT((value),1,5))
#define UDMA_I2S_I2S_TX_CFG_PENDING_SET(value,field)       (ARCHI_BINSERT((value),(field),1,5))
#define UDMA_I2S_I2S_TX_CFG_PENDING(val)                   ((val) << 5)

#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_GET(value) (ARCHI_BEXTRACTU((value),8,0))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_GETS(value) (ARCHI_BEXTRACT((value),8,0))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV_SET(value,field) (ARCHI_BINSERT((value),(field),8,0))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_DIV(val)      ((val) << 0)

#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_GET(value) (ARCHI_BEXTRACTU((value),8,8))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_GETS(value) (ARCHI_BEXTRACT((value),8,8))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV_SET(value,field) (ARCHI_BINSERT((value),(field),8,8))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_DIV(val)       ((val) << 8)

#define UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_GET(value) (ARCHI_BEXTRACTU((value),8,16))
#define UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_GETS(value) (ARCHI_BEXTRACT((value),8,16))
#define UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV_SET(value,field) (ARCHI_BINSERT((value),(field),8,16))
#define UDMA_I2S_I2S_CLKCFG_SETUP_COMMON_CLK_DIV(val)      ((val) << 16)

#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_GET(value)  (ARCHI_BEXTRACTU((value),1,24))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_GETS(value) (ARCHI_BEXTRACT((value),1,24))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN_SET(value,field) (ARCHI_BINSERT((value),(field),1,24))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_CLK_EN(val)        ((val) << 24)

#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_GET(value) (ARCHI_BEXTRACTU((value),1,25))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_GETS(value) (ARCHI_BEXTRACT((value),1,25))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN_SET(value,field) (ARCHI_BINSERT((value),(field),1,25))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_CLK_EN(val)       ((val) << 25)

#define UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_GET(value)    (ARCHI_BEXTRACTU((value),1,26))
#define UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_GETS(value)   (ARCHI_BEXTRACT((value),1,26))
#define UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN_SET(value,field) (ARCHI_BINSERT((value),(field),1,26))
#define UDMA_I2S_I2S_CLKCFG_SETUP_PDM_CLK_EN(val)          ((val) << 26)

#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_GET(value)     (ARCHI_BEXTRACTU((value),1,28))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_GETS(value)    (ARCHI_BEXTRACT((value),1,28))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT_SET(value,field) (ARCHI_BINSERT((value),(field),1,28))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_EXT(val)           ((val) << 28)

#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_GET(value)     (ARCHI_BEXTRACTU((value),1,29))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_GETS(value)    (ARCHI_BEXTRACT((value),1,29))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM_SET(value,field) (ARCHI_BINSERT((value),(field),1,29))
#define UDMA_I2S_I2S_CLKCFG_SETUP_SLAVE_NUM(val)           ((val) << 29)

#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_GET(value)    (ARCHI_BEXTRACTU((value),1,30))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_GETS(value)   (ARCHI_BEXTRACT((value),1,30))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT_SET(value,field) (ARCHI_BINSERT((value),(field),1,30))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_EXT(val)          ((val) << 30)

#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_GET(value)    (ARCHI_BEXTRACTU((value),1,31))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_GETS(value)   (ARCHI_BEXTRACT((value),1,31))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM_SET(value,field) (ARCHI_BINSERT((value),(field),1,31))
#define UDMA_I2S_I2S_CLKCFG_SETUP_MASTER_NUM(val)          ((val) << 31)

#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_GET(value)      (ARCHI_BEXTRACTU((value),3,0))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_GETS(value)     (ARCHI_BEXTRACT((value),3,0))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS_SET(value,field) (ARCHI_BINSERT((value),(field),3,0))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_WORDS(val)            ((val) << 0)

#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_GET(value)       (ARCHI_BEXTRACTU((value),5,8))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_GETS(value)      (ARCHI_BEXTRACT((value),5,8))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS_SET(value,field) (ARCHI_BINSERT((value),(field),5,8))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_BITS(val)             ((val) << 8)

#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_GET(value)        (ARCHI_BEXTRACTU((value),1,16))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_GETS(value)       (ARCHI_BEXTRACT((value),1,16))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB_SET(value,field)  (ARCHI_BINSERT((value),(field),1,16))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_LSB(val)              ((val) << 16)

#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_GET(value)        (ARCHI_BEXTRACTU((value),1,17))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_GETS(value)       (ARCHI_BEXTRACT((value),1,17))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH_SET(value,field)  (ARCHI_BINSERT((value),(field),1,17))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_2CH(val)              ((val) << 17)

#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_GET(value)         (ARCHI_BEXTRACTU((value),1,31))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_GETS(value)        (ARCHI_BEXTRACT((value),1,31))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN_SET(value,field)   (ARCHI_BINSERT((value),(field),1,31))
#define UDMA_I2S_I2S_SLV_SETUP_SLAVE_EN(val)               ((val) << 31)

#define UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_GET(value)     (ARCHI_BEXTRACTU((value),3,0))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_GETS(value)    (ARCHI_BEXTRACT((value),3,0))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS_SET(value,field) (ARCHI_BINSERT((value),(field),3,0))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_WORDS(val)           ((val) << 0)

#define UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_GET(value)      (ARCHI_BEXTRACTU((value),5,8))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_GETS(value)     (ARCHI_BEXTRACT((value),5,8))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_BITS_SET(value,field) (ARCHI_BINSERT((value),(field),5,8))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_BITS(val)            ((val) << 8)

#define UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_GET(value)       (ARCHI_BEXTRACTU((value),1,16))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_GETS(value)      (ARCHI_BEXTRACT((value),1,16))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_LSB_SET(value,field) (ARCHI_BINSERT((value),(field),1,16))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_LSB(val)             ((val) << 16)

#define UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_GET(value)       (ARCHI_BEXTRACTU((value),1,17))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_GETS(value)      (ARCHI_BEXTRACT((value),1,17))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_2CH_SET(value,field) (ARCHI_BINSERT((value),(field),1,17))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_2CH(val)             ((val) << 17)

#define UDMA_I2S_I2S_MST_SETUP_MASTER_EN_GET(value)        (ARCHI_BEXTRACTU((value),1,31))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_EN_GETS(value)       (ARCHI_BEXTRACT((value),1,31))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_EN_SET(value,field)  (ARCHI_BINSERT((value),(field),1,31))
#define UDMA_I2S_I2S_MST_SETUP_MASTER_EN(val)              ((val) << 31)

#define UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_GET(value)        (ARCHI_BEXTRACTU((value),3,0))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_GETS(value)       (ARCHI_BEXTRACT((value),3,0))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT_SET(value,field)  (ARCHI_BINSERT((value),(field),3,0))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_SHIFT(val)              ((val) << 0)

#define UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_GET(value)   (ARCHI_BEXTRACTU((value),10,3))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_GETS(value)  (ARCHI_BEXTRACT((value),10,3))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION_SET(value,field) (ARCHI_BINSERT((value),(field),10,3))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_DECIMATION(val)         ((val) << 3)

#define UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_GET(value)         (ARCHI_BEXTRACTU((value),2,13))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_GETS(value)        (ARCHI_BEXTRACT((value),2,13))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_MODE_SET(value,field)   (ARCHI_BINSERT((value),(field),2,13))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_MODE(val)               ((val) << 13)

#define UDMA_I2S_I2S_PDM_SETUP_PDM_EN_GET(value)           (ARCHI_BEXTRACTU((value),1,31))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_EN_GETS(value)          (ARCHI_BEXTRACT((value),1,31))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_EN_SET(value,field)     (ARCHI_BINSERT((value),(field),1,31))
#define UDMA_I2S_I2S_PDM_SETUP_PDM_EN(val)                 ((val) << 31)

#endif

#endif
