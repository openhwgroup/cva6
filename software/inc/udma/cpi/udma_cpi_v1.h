
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

#ifndef __INCLUDE_ARCHI_UDMA_CPI_UDMA_CPI_V1_H__
#define __INCLUDE_ARCHI_UDMA_CPI_UDMA_CPI_V1_H__

#ifndef LANGUAGE_ASSEMBLY

#include <stdint.h>
#include "archi/utils.h"

#endif




//
// REGISTERS
//

// RX Camera uDMA transfer address of associated buffer register
#define UDMA_CPI_CAM_RX_SADDR_OFFSET             0x0

// RX Camera uDMA transfer size of buffer register
#define UDMA_CPI_CAM_RX_SIZE_OFFSET              0x4

// RX Camera uDMA transfer configuration register
#define UDMA_CPI_CAM_RX_CFG_OFFSET               0x8

// -
#define UDMA_CPI_CAM_RX_INITCFG_OFFSET           0xc

// -
#define UDMA_CPI_CAM_TX_SADDR_OFFSET             0x10

// -
#define UDMA_CPI_CAM_TX_SIZE_OFFSET              0x14

// -
#define UDMA_CPI_CAM_TX_CFG_OFFSET               0x18

// -
#define UDMA_CPI_CAM_TX_INITCFG_OFFSET           0x1c

// Global configuration register
#define UDMA_CPI_CAM_CFG_GLOB_OFFSET             0x20

// Lower Left corner configuration register
#define UDMA_CPI_CAM_CFG_LL_OFFSET               0x24

// Upper Right corner configuration register
#define UDMA_CPI_CAM_CFG_UR_OFFSET               0x28

// Horizontal Resolution configuration register
#define UDMA_CPI_CAM_CFG_SIZE_OFFSET             0x2c

// RGB coefficients configuration register
#define UDMA_CPI_CAM_CFG_FILTER_OFFSET           0x30

// VSYNC Polarity register
#define UDMA_CPI_CAM_VSYNC_POLARITY_OFFSET       0x34



//
// REGISTERS FIELDS
//

// Configure pointer to memory buffer: - Read: value of the pointer until transfer is over. Else returns 0 - Write: set Address Pointer to memory buffer start address (access: R/W)
#define UDMA_CPI_CAM_RX_SADDR_RX_SADDR_BIT                           0
#define UDMA_CPI_CAM_RX_SADDR_RX_SADDR_WIDTH                         16
#define UDMA_CPI_CAM_RX_SADDR_RX_SADDR_MASK                          0xffff

// Buffer size in bytes. (128kBytes maximum) - Read: buffer size left - Write: set buffer size NOTE: Careful with size in byte. If you use uncompressed pixel data mapped on 16 bits, you have to declare buffer size in bytes even if buffer type is short. (access: R/W)
#define UDMA_CPI_CAM_RX_SIZE_RX_SIZE_BIT                             0
#define UDMA_CPI_CAM_RX_SIZE_RX_SIZE_WIDTH                           17
#define UDMA_CPI_CAM_RX_SIZE_RX_SIZE_MASK                            0x1ffff

// Channel continuous mode: -1'b0: disable -1'b1: enable At the end of the buffer the uDMA reloads the address and size and starts a new transfer. (access: R/W)
#define UDMA_CPI_CAM_RX_CFG_CONTINOUS_BIT                            0
#define UDMA_CPI_CAM_RX_CFG_CONTINOUS_WIDTH                          1
#define UDMA_CPI_CAM_RX_CFG_CONTINOUS_MASK                           0x1

// Channel transfer size used to increment uDMA buffer address pointer: - 2'b00: +1 (8 bits) - 2'b01: +2 (16 bits) - 2'b10: +4 (32 bits) - 2'b11: +0 (access: R/W)
#define UDMA_CPI_CAM_RX_CFG_DATASIZE_BIT                             1
#define UDMA_CPI_CAM_RX_CFG_DATASIZE_WIDTH                           2
#define UDMA_CPI_CAM_RX_CFG_DATASIZE_MASK                            0x6

// Channel enable and start transfer: -1'b0: disable -1'b1: enable This signal is used also to queue a transfer if one is already ongoing. (access: R/W)
#define UDMA_CPI_CAM_RX_CFG_EN_BIT                                   4
#define UDMA_CPI_CAM_RX_CFG_EN_WIDTH                                 1
#define UDMA_CPI_CAM_RX_CFG_EN_MASK                                  0x10

// Transfer pending in queue status flag: -1'b0: free -1'b1: pending (access: R)
#define UDMA_CPI_CAM_RX_CFG_PENDING_BIT                              5
#define UDMA_CPI_CAM_RX_CFG_PENDING_WIDTH                            1
#define UDMA_CPI_CAM_RX_CFG_PENDING_MASK                             0x20

// Channel clear and stop transfer: -1'b0: disable -1'b1: enable (access: W)
#define UDMA_CPI_CAM_RX_CFG_CLR_BIT                                  6
#define UDMA_CPI_CAM_RX_CFG_CLR_WIDTH                                1
#define UDMA_CPI_CAM_RX_CFG_CLR_MASK                                 0x40

// Frame dropping: - 1'b0: disable - 1'b1: enable (access: R/W)
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_BIT                       0
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_WIDTH                     1
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_MASK                      0x1

// Sets how many frames should be dropped after each received. (access: R/W)
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_BIT                      1
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_WIDTH                    6
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_MASK                     0x7e

// Input frame slicing: - 1'b0: disable - 1'b1: enable (access: R/W)
#define UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_BIT                      7
#define UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_WIDTH                    1
#define UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_MASK                     0x80

// Input frame format: - 3'b000: RGB565 - 3'b001: RGB555 - 3'b010: RGB444 - 3'b100: BYPASS_LITEND - 3’b101: BYPASS_BIGEND (access: R/W)
#define UDMA_CPI_CAM_CFG_GLOB_FORMAT_BIT                             8
#define UDMA_CPI_CAM_CFG_GLOB_FORMAT_WIDTH                           3
#define UDMA_CPI_CAM_CFG_GLOB_FORMAT_MASK                            0x700

// Right shift of final pixel value (DivFactor) NOTE: not used if FORMAT == BYPASS (access: R/W)
#define UDMA_CPI_CAM_CFG_GLOB_SHIFT_BIT                              11
#define UDMA_CPI_CAM_CFG_GLOB_SHIFT_WIDTH                            4
#define UDMA_CPI_CAM_CFG_GLOB_SHIFT_MASK                             0x7800

// Enable data rx from camera interface.  The enable/disable happens only at the start of a frame. - 1'b0: disable - 1'b1: enable (access: R/W)
#define UDMA_CPI_CAM_CFG_GLOB_EN_BIT                                 31
#define UDMA_CPI_CAM_CFG_GLOB_EN_WIDTH                               1
#define UDMA_CPI_CAM_CFG_GLOB_EN_MASK                                0x80000000

// X coordinate of lower left corner of slice (access: R/W)
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_BIT                       0
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_WIDTH                     16
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_MASK                      0xffff

// Y coordinate of lower left corner of slice (access: R/W)
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_BIT                       16
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_WIDTH                     16
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_MASK                      0xffff0000

// X coordinate of upper right corner of slice (access: R/W)
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_BIT                       0
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_WIDTH                     16
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_MASK                      0xffff

// Y coordinate of upper right corner of slice (access: R/W)
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_BIT                       16
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_WIDTH                     16
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_MASK                      0xffff0000

// Horizontal Resolution. It is used for slice mode. Value set into the bitfield must be equal to (rowlen-1). (access: R/W)
#define UDMA_CPI_CAM_CFG_SIZE_ROWLEN_BIT                             16
#define UDMA_CPI_CAM_CFG_SIZE_ROWLEN_WIDTH                           16
#define UDMA_CPI_CAM_CFG_SIZE_ROWLEN_MASK                            0xffff0000

// Coefficient that multiplies the B component NOTE: not used if FORMAT == BYPASS (access: R/W)
#define UDMA_CPI_CAM_CFG_FILTER_B_COEFF_BIT                          0
#define UDMA_CPI_CAM_CFG_FILTER_B_COEFF_WIDTH                        8
#define UDMA_CPI_CAM_CFG_FILTER_B_COEFF_MASK                         0xff

// Coefficient that multiplies the G component NOTE: not used if FORMAT == BYPASS (access: R/W)
#define UDMA_CPI_CAM_CFG_FILTER_G_COEFF_BIT                          8
#define UDMA_CPI_CAM_CFG_FILTER_G_COEFF_WIDTH                        8
#define UDMA_CPI_CAM_CFG_FILTER_G_COEFF_MASK                         0xff00

// Coefficient that multiplies the R component NOTE: not used if FORMAT == BYPASS (access: R/W)
#define UDMA_CPI_CAM_CFG_FILTER_R_COEFF_BIT                          16
#define UDMA_CPI_CAM_CFG_FILTER_R_COEFF_WIDTH                        8
#define UDMA_CPI_CAM_CFG_FILTER_R_COEFF_MASK                         0xff0000

// Set vsync polarity of CPI. - 1'b0: Active 0 - 1'b1: Active 1 (access: R/W)
#define UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_BIT               0
#define UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_WIDTH             1
#define UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_MASK              0x1



//
// REGISTERS STRUCTS
//

#ifndef LANGUAGE_ASSEMBLY

typedef union {
  struct {
    unsigned int rx_saddr        :16; // Configure pointer to memory buffer: - Read: value of the pointer until transfer is over. Else returns 0 - Write: set Address Pointer to memory buffer start address
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_rx_saddr_t;

typedef union {
  struct {
    unsigned int rx_size         :17; // Buffer size in bytes. (128kBytes maximum) - Read: buffer size left - Write: set buffer size NOTE: Careful with size in byte. If you use uncompressed pixel data mapped on 16 bits, you have to declare buffer size in bytes even if buffer type is short.
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_rx_size_t;

typedef union {
  struct {
    unsigned int continous       :1 ; // Channel continuous mode: -1'b0: disable -1'b1: enable At the end of the buffer the uDMA reloads the address and size and starts a new transfer.
    unsigned int datasize        :2 ; // Channel transfer size used to increment uDMA buffer address pointer: - 2'b00: +1 (8 bits) - 2'b01: +2 (16 bits) - 2'b10: +4 (32 bits) - 2'b11: +0
    unsigned int padding0:1 ;
    unsigned int en              :1 ; // Channel enable and start transfer: -1'b0: disable -1'b1: enable This signal is used also to queue a transfer if one is already ongoing.
    unsigned int pending         :1 ; // Transfer pending in queue status flag: -1'b0: free -1'b1: pending
    unsigned int clr             :1 ; // Channel clear and stop transfer: -1'b0: disable -1'b1: enable
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_rx_cfg_t;

typedef union {
  struct {
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_rx_initcfg_t;

typedef union {
  struct {
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_tx_saddr_t;

typedef union {
  struct {
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_tx_size_t;

typedef union {
  struct {
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_tx_cfg_t;

typedef union {
  struct {
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_tx_initcfg_t;

typedef union {
  struct {
    unsigned int framedrop_en    :1 ; // Frame dropping: - 1'b0: disable - 1'b1: enable
    unsigned int framedrop_val   :6 ; // Sets how many frames should be dropped after each received.
    unsigned int frameslice_en   :1 ; // Input frame slicing: - 1'b0: disable - 1'b1: enable
    unsigned int format          :3 ; // Input frame format: - 3'b000: RGB565 - 3'b001: RGB555 - 3'b010: RGB444 - 3'b100: BYPASS_LITEND - 3’b101: BYPASS_BIGEND
    unsigned int shift           :4 ; // Right shift of final pixel value (DivFactor) NOTE: not used if FORMAT == BYPASS
    unsigned int padding0:16;
    unsigned int en              :1 ; // Enable data rx from camera interface.  The enable/disable happens only at the start of a frame. - 1'b0: disable - 1'b1: enable
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_cfg_glob_t;

typedef union {
  struct {
    unsigned int frameslice_llx  :16; // X coordinate of lower left corner of slice
    unsigned int frameslice_lly  :16; // Y coordinate of lower left corner of slice
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_cfg_ll_t;

typedef union {
  struct {
    unsigned int frameslice_urx  :16; // X coordinate of upper right corner of slice
    unsigned int frameslice_ury  :16; // Y coordinate of upper right corner of slice
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_cfg_ur_t;

typedef union {
  struct {
    unsigned int padding0:16;
    unsigned int rowlen          :16; // Horizontal Resolution. It is used for slice mode. Value set into the bitfield must be equal to (rowlen-1).
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_cfg_size_t;

typedef union {
  struct {
    unsigned int b_coeff         :8 ; // Coefficient that multiplies the B component NOTE: not used if FORMAT == BYPASS
    unsigned int g_coeff         :8 ; // Coefficient that multiplies the G component NOTE: not used if FORMAT == BYPASS
    unsigned int r_coeff         :8 ; // Coefficient that multiplies the R component NOTE: not used if FORMAT == BYPASS
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_cfg_filter_t;

typedef union {
  struct {
    unsigned int vsync_polarity  :1 ; // Set vsync polarity of CPI. - 1'b0: Active 0 - 1'b1: Active 1
  };
  unsigned int raw;
} __attribute__((packed)) udma_cpi_cam_vsync_polarity_t;

#endif



//
// REGISTERS STRUCTS
//

#ifdef __GVSOC__

class vp_udma_cpi_cam_rx_saddr : public vp::reg_32
{
public:
  inline void rx_saddr_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_RX_SADDR_RX_SADDR_BIT, UDMA_CPI_CAM_RX_SADDR_RX_SADDR_WIDTH); }
  inline uint32_t rx_saddr_get() { return this->get_field(UDMA_CPI_CAM_RX_SADDR_RX_SADDR_BIT, UDMA_CPI_CAM_RX_SADDR_RX_SADDR_WIDTH); }
};

class vp_udma_cpi_cam_rx_size : public vp::reg_32
{
public:
  inline void rx_size_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_RX_SIZE_RX_SIZE_BIT, UDMA_CPI_CAM_RX_SIZE_RX_SIZE_WIDTH); }
  inline uint32_t rx_size_get() { return this->get_field(UDMA_CPI_CAM_RX_SIZE_RX_SIZE_BIT, UDMA_CPI_CAM_RX_SIZE_RX_SIZE_WIDTH); }
};

class vp_udma_cpi_cam_rx_cfg : public vp::reg_32
{
public:
  inline void continous_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_RX_CFG_CONTINOUS_BIT, UDMA_CPI_CAM_RX_CFG_CONTINOUS_WIDTH); }
  inline uint32_t continous_get() { return this->get_field(UDMA_CPI_CAM_RX_CFG_CONTINOUS_BIT, UDMA_CPI_CAM_RX_CFG_CONTINOUS_WIDTH); }
  inline void datasize_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_RX_CFG_DATASIZE_BIT, UDMA_CPI_CAM_RX_CFG_DATASIZE_WIDTH); }
  inline uint32_t datasize_get() { return this->get_field(UDMA_CPI_CAM_RX_CFG_DATASIZE_BIT, UDMA_CPI_CAM_RX_CFG_DATASIZE_WIDTH); }
  inline void en_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_RX_CFG_EN_BIT, UDMA_CPI_CAM_RX_CFG_EN_WIDTH); }
  inline uint32_t en_get() { return this->get_field(UDMA_CPI_CAM_RX_CFG_EN_BIT, UDMA_CPI_CAM_RX_CFG_EN_WIDTH); }
  inline void pending_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_RX_CFG_PENDING_BIT, UDMA_CPI_CAM_RX_CFG_PENDING_WIDTH); }
  inline uint32_t pending_get() { return this->get_field(UDMA_CPI_CAM_RX_CFG_PENDING_BIT, UDMA_CPI_CAM_RX_CFG_PENDING_WIDTH); }
  inline void clr_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_RX_CFG_CLR_BIT, UDMA_CPI_CAM_RX_CFG_CLR_WIDTH); }
  inline uint32_t clr_get() { return this->get_field(UDMA_CPI_CAM_RX_CFG_CLR_BIT, UDMA_CPI_CAM_RX_CFG_CLR_WIDTH); }
};

class vp_udma_cpi_cam_cfg_glob : public vp::reg_32
{
public:
  inline void framedrop_en_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_BIT, UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_WIDTH); }
  inline uint32_t framedrop_en_get() { return this->get_field(UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_BIT, UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_WIDTH); }
  inline void framedrop_val_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_BIT, UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_WIDTH); }
  inline uint32_t framedrop_val_get() { return this->get_field(UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_BIT, UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_WIDTH); }
  inline void frameslice_en_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_BIT, UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_WIDTH); }
  inline uint32_t frameslice_en_get() { return this->get_field(UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_BIT, UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_WIDTH); }
  inline void format_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_GLOB_FORMAT_BIT, UDMA_CPI_CAM_CFG_GLOB_FORMAT_WIDTH); }
  inline uint32_t format_get() { return this->get_field(UDMA_CPI_CAM_CFG_GLOB_FORMAT_BIT, UDMA_CPI_CAM_CFG_GLOB_FORMAT_WIDTH); }
  inline void shift_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_GLOB_SHIFT_BIT, UDMA_CPI_CAM_CFG_GLOB_SHIFT_WIDTH); }
  inline uint32_t shift_get() { return this->get_field(UDMA_CPI_CAM_CFG_GLOB_SHIFT_BIT, UDMA_CPI_CAM_CFG_GLOB_SHIFT_WIDTH); }
  inline void en_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_GLOB_EN_BIT, UDMA_CPI_CAM_CFG_GLOB_EN_WIDTH); }
  inline uint32_t en_get() { return this->get_field(UDMA_CPI_CAM_CFG_GLOB_EN_BIT, UDMA_CPI_CAM_CFG_GLOB_EN_WIDTH); }
};

class vp_udma_cpi_cam_cfg_ll : public vp::reg_32
{
public:
  inline void frameslice_llx_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_BIT, UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_WIDTH); }
  inline uint32_t frameslice_llx_get() { return this->get_field(UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_BIT, UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_WIDTH); }
  inline void frameslice_lly_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_BIT, UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_WIDTH); }
  inline uint32_t frameslice_lly_get() { return this->get_field(UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_BIT, UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_WIDTH); }
};

class vp_udma_cpi_cam_cfg_ur : public vp::reg_32
{
public:
  inline void frameslice_urx_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_BIT, UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_WIDTH); }
  inline uint32_t frameslice_urx_get() { return this->get_field(UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_BIT, UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_WIDTH); }
  inline void frameslice_ury_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_BIT, UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_WIDTH); }
  inline uint32_t frameslice_ury_get() { return this->get_field(UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_BIT, UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_WIDTH); }
};

class vp_udma_cpi_cam_cfg_size : public vp::reg_32
{
public:
  inline void rowlen_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_SIZE_ROWLEN_BIT, UDMA_CPI_CAM_CFG_SIZE_ROWLEN_WIDTH); }
  inline uint32_t rowlen_get() { return this->get_field(UDMA_CPI_CAM_CFG_SIZE_ROWLEN_BIT, UDMA_CPI_CAM_CFG_SIZE_ROWLEN_WIDTH); }
};

class vp_udma_cpi_cam_cfg_filter : public vp::reg_32
{
public:
  inline void b_coeff_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_FILTER_B_COEFF_BIT, UDMA_CPI_CAM_CFG_FILTER_B_COEFF_WIDTH); }
  inline uint32_t b_coeff_get() { return this->get_field(UDMA_CPI_CAM_CFG_FILTER_B_COEFF_BIT, UDMA_CPI_CAM_CFG_FILTER_B_COEFF_WIDTH); }
  inline void g_coeff_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_FILTER_G_COEFF_BIT, UDMA_CPI_CAM_CFG_FILTER_G_COEFF_WIDTH); }
  inline uint32_t g_coeff_get() { return this->get_field(UDMA_CPI_CAM_CFG_FILTER_G_COEFF_BIT, UDMA_CPI_CAM_CFG_FILTER_G_COEFF_WIDTH); }
  inline void r_coeff_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_CFG_FILTER_R_COEFF_BIT, UDMA_CPI_CAM_CFG_FILTER_R_COEFF_WIDTH); }
  inline uint32_t r_coeff_get() { return this->get_field(UDMA_CPI_CAM_CFG_FILTER_R_COEFF_BIT, UDMA_CPI_CAM_CFG_FILTER_R_COEFF_WIDTH); }
};

class vp_udma_cpi_cam_vsync_polarity : public vp::reg_32
{
public:
  inline void vsync_polarity_set(uint32_t value) { this->set_field(value, UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_BIT, UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_WIDTH); }
  inline uint32_t vsync_polarity_get() { return this->get_field(UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_BIT, UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_WIDTH); }
};

#endif



//
// REGISTERS GLOBAL STRUCT
//

#ifndef LANGUAGE_ASSEMBLY

typedef struct {
  unsigned int cam_rx_saddr    ; // RX Camera uDMA transfer address of associated buffer register
  unsigned int cam_rx_size     ; // RX Camera uDMA transfer size of buffer register
  unsigned int cam_rx_cfg      ; // RX Camera uDMA transfer configuration register
  unsigned int cam_rx_initcfg  ; // -
  unsigned int cam_tx_saddr    ; // -
  unsigned int cam_tx_size     ; // -
  unsigned int cam_tx_cfg      ; // -
  unsigned int cam_tx_initcfg  ; // -
  unsigned int cam_cfg_glob    ; // Global configuration register
  unsigned int cam_cfg_ll      ; // Lower Left corner configuration register
  unsigned int cam_cfg_ur      ; // Upper Right corner configuration register
  unsigned int cam_cfg_size    ; // Horizontal Resolution configuration register
  unsigned int cam_cfg_filter  ; // RGB coefficients configuration register
  unsigned int cam_vsync_polarity; // VSYNC Polarity register
} __attribute__((packed)) udma_cpi_udma_cpi_t;

#endif



//
// REGISTERS ACCESS FUNCTIONS
//

#ifndef LANGUAGE_ASSEMBLY

static inline uint32_t udma_cpi_cam_rx_saddr_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_RX_SADDR_OFFSET); }
static inline void udma_cpi_cam_rx_saddr_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_RX_SADDR_OFFSET, value); }

static inline uint32_t udma_cpi_cam_rx_size_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_RX_SIZE_OFFSET); }
static inline void udma_cpi_cam_rx_size_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_RX_SIZE_OFFSET, value); }

static inline uint32_t udma_cpi_cam_rx_cfg_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_RX_CFG_OFFSET); }
static inline void udma_cpi_cam_rx_cfg_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_RX_CFG_OFFSET, value); }

static inline uint32_t udma_cpi_cam_rx_initcfg_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_RX_INITCFG_OFFSET); }
static inline void udma_cpi_cam_rx_initcfg_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_RX_INITCFG_OFFSET, value); }

static inline uint32_t udma_cpi_cam_tx_saddr_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_TX_SADDR_OFFSET); }
static inline void udma_cpi_cam_tx_saddr_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_TX_SADDR_OFFSET, value); }

static inline uint32_t udma_cpi_cam_tx_size_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_TX_SIZE_OFFSET); }
static inline void udma_cpi_cam_tx_size_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_TX_SIZE_OFFSET, value); }

static inline uint32_t udma_cpi_cam_tx_cfg_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_TX_CFG_OFFSET); }
static inline void udma_cpi_cam_tx_cfg_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_TX_CFG_OFFSET, value); }

static inline uint32_t udma_cpi_cam_tx_initcfg_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_TX_INITCFG_OFFSET); }
static inline void udma_cpi_cam_tx_initcfg_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_TX_INITCFG_OFFSET, value); }

static inline uint32_t udma_cpi_cam_cfg_glob_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_CFG_GLOB_OFFSET); }
static inline void udma_cpi_cam_cfg_glob_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_CFG_GLOB_OFFSET, value); }

static inline uint32_t udma_cpi_cam_cfg_ll_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_CFG_LL_OFFSET); }
static inline void udma_cpi_cam_cfg_ll_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_CFG_LL_OFFSET, value); }

static inline uint32_t udma_cpi_cam_cfg_ur_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_CFG_UR_OFFSET); }
static inline void udma_cpi_cam_cfg_ur_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_CFG_UR_OFFSET, value); }

static inline uint32_t udma_cpi_cam_cfg_size_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_CFG_SIZE_OFFSET); }
static inline void udma_cpi_cam_cfg_size_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_CFG_SIZE_OFFSET, value); }

static inline uint32_t udma_cpi_cam_cfg_filter_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_CFG_FILTER_OFFSET); }
static inline void udma_cpi_cam_cfg_filter_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_CFG_FILTER_OFFSET, value); }

static inline uint32_t udma_cpi_cam_vsync_polarity_get(uint32_t base) { return ARCHI_READ(base, UDMA_CPI_CAM_VSYNC_POLARITY_OFFSET); }
static inline void udma_cpi_cam_vsync_polarity_set(uint32_t base, uint32_t value) { ARCHI_WRITE(base, UDMA_CPI_CAM_VSYNC_POLARITY_OFFSET, value); }

#endif



//
// REGISTERS FIELDS MACROS
//

#ifndef LANGUAGE_ASSEMBLY

#define UDMA_CPI_CAM_RX_SADDR_RX_SADDR_GET(value)          (ARCHI_BEXTRACTU((value),16,0))
#define UDMA_CPI_CAM_RX_SADDR_RX_SADDR_GETS(value)         (ARCHI_BEXTRACT((value),16,0))
#define UDMA_CPI_CAM_RX_SADDR_RX_SADDR_SET(value,field)    (ARCHI_BINSERT((value),(field),16,0))
#define UDMA_CPI_CAM_RX_SADDR_RX_SADDR(val)                ((val) << 0)

#define UDMA_CPI_CAM_RX_SIZE_RX_SIZE_GET(value)            (ARCHI_BEXTRACTU((value),17,0))
#define UDMA_CPI_CAM_RX_SIZE_RX_SIZE_GETS(value)           (ARCHI_BEXTRACT((value),17,0))
#define UDMA_CPI_CAM_RX_SIZE_RX_SIZE_SET(value,field)      (ARCHI_BINSERT((value),(field),17,0))
#define UDMA_CPI_CAM_RX_SIZE_RX_SIZE(val)                  ((val) << 0)

#define UDMA_CPI_CAM_RX_CFG_CONTINOUS_GET(value)           (ARCHI_BEXTRACTU((value),1,0))
#define UDMA_CPI_CAM_RX_CFG_CONTINOUS_GETS(value)          (ARCHI_BEXTRACT((value),1,0))
#define UDMA_CPI_CAM_RX_CFG_CONTINOUS_SET(value,field)     (ARCHI_BINSERT((value),(field),1,0))
#define UDMA_CPI_CAM_RX_CFG_CONTINOUS(val)                 ((val) << 0)

#define UDMA_CPI_CAM_RX_CFG_DATASIZE_GET(value)            (ARCHI_BEXTRACTU((value),2,1))
#define UDMA_CPI_CAM_RX_CFG_DATASIZE_GETS(value)           (ARCHI_BEXTRACT((value),2,1))
#define UDMA_CPI_CAM_RX_CFG_DATASIZE_SET(value,field)      (ARCHI_BINSERT((value),(field),2,1))
#define UDMA_CPI_CAM_RX_CFG_DATASIZE(val)                  ((val) << 1)

#define UDMA_CPI_CAM_RX_CFG_EN_GET(value)                  (ARCHI_BEXTRACTU((value),1,4))
#define UDMA_CPI_CAM_RX_CFG_EN_GETS(value)                 (ARCHI_BEXTRACT((value),1,4))
#define UDMA_CPI_CAM_RX_CFG_EN_SET(value,field)            (ARCHI_BINSERT((value),(field),1,4))
#define UDMA_CPI_CAM_RX_CFG_EN(val)                        ((val) << 4)

#define UDMA_CPI_CAM_RX_CFG_PENDING_GET(value)             (ARCHI_BEXTRACTU((value),1,5))
#define UDMA_CPI_CAM_RX_CFG_PENDING_GETS(value)            (ARCHI_BEXTRACT((value),1,5))
#define UDMA_CPI_CAM_RX_CFG_PENDING_SET(value,field)       (ARCHI_BINSERT((value),(field),1,5))
#define UDMA_CPI_CAM_RX_CFG_PENDING(val)                   ((val) << 5)

#define UDMA_CPI_CAM_RX_CFG_CLR_GET(value)                 (ARCHI_BEXTRACTU((value),1,6))
#define UDMA_CPI_CAM_RX_CFG_CLR_GETS(value)                (ARCHI_BEXTRACT((value),1,6))
#define UDMA_CPI_CAM_RX_CFG_CLR_SET(value,field)           (ARCHI_BINSERT((value),(field),1,6))
#define UDMA_CPI_CAM_RX_CFG_CLR(val)                       ((val) << 6)

#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_GET(value)      (ARCHI_BEXTRACTU((value),1,0))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_GETS(value)     (ARCHI_BEXTRACT((value),1,0))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN_SET(value,field) (ARCHI_BINSERT((value),(field),1,0))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_EN(val)            ((val) << 0)

#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_GET(value)     (ARCHI_BEXTRACTU((value),6,1))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_GETS(value)    (ARCHI_BEXTRACT((value),6,1))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL_SET(value,field) (ARCHI_BINSERT((value),(field),6,1))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMEDROP_VAL(val)           ((val) << 1)

#define UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_GET(value)     (ARCHI_BEXTRACTU((value),1,7))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_GETS(value)    (ARCHI_BEXTRACT((value),1,7))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN_SET(value,field) (ARCHI_BINSERT((value),(field),1,7))
#define UDMA_CPI_CAM_CFG_GLOB_FRAMESLICE_EN(val)           ((val) << 7)

#define UDMA_CPI_CAM_CFG_GLOB_FORMAT_GET(value)            (ARCHI_BEXTRACTU((value),3,8))
#define UDMA_CPI_CAM_CFG_GLOB_FORMAT_GETS(value)           (ARCHI_BEXTRACT((value),3,8))
#define UDMA_CPI_CAM_CFG_GLOB_FORMAT_SET(value,field)      (ARCHI_BINSERT((value),(field),3,8))
#define UDMA_CPI_CAM_CFG_GLOB_FORMAT(val)                  ((val) << 8)

#define UDMA_CPI_CAM_CFG_GLOB_SHIFT_GET(value)             (ARCHI_BEXTRACTU((value),4,11))
#define UDMA_CPI_CAM_CFG_GLOB_SHIFT_GETS(value)            (ARCHI_BEXTRACT((value),4,11))
#define UDMA_CPI_CAM_CFG_GLOB_SHIFT_SET(value,field)       (ARCHI_BINSERT((value),(field),4,11))
#define UDMA_CPI_CAM_CFG_GLOB_SHIFT(val)                   ((val) << 11)

#define UDMA_CPI_CAM_CFG_GLOB_EN_GET(value)                (ARCHI_BEXTRACTU((value),1,31))
#define UDMA_CPI_CAM_CFG_GLOB_EN_GETS(value)               (ARCHI_BEXTRACT((value),1,31))
#define UDMA_CPI_CAM_CFG_GLOB_EN_SET(value,field)          (ARCHI_BINSERT((value),(field),1,31))
#define UDMA_CPI_CAM_CFG_GLOB_EN(val)                      ((val) << 31)

#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_GET(value)      (ARCHI_BEXTRACTU((value),16,0))
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_GETS(value)     (ARCHI_BEXTRACT((value),16,0))
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX_SET(value,field) (ARCHI_BINSERT((value),(field),16,0))
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLX(val)            ((val) << 0)

#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_GET(value)      (ARCHI_BEXTRACTU((value),16,16))
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_GETS(value)     (ARCHI_BEXTRACT((value),16,16))
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY_SET(value,field) (ARCHI_BINSERT((value),(field),16,16))
#define UDMA_CPI_CAM_CFG_LL_FRAMESLICE_LLY(val)            ((val) << 16)

#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_GET(value)      (ARCHI_BEXTRACTU((value),16,0))
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_GETS(value)     (ARCHI_BEXTRACT((value),16,0))
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX_SET(value,field) (ARCHI_BINSERT((value),(field),16,0))
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URX(val)            ((val) << 0)

#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_GET(value)      (ARCHI_BEXTRACTU((value),16,16))
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_GETS(value)     (ARCHI_BEXTRACT((value),16,16))
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY_SET(value,field) (ARCHI_BINSERT((value),(field),16,16))
#define UDMA_CPI_CAM_CFG_UR_FRAMESLICE_URY(val)            ((val) << 16)

#define UDMA_CPI_CAM_CFG_SIZE_ROWLEN_GET(value)            (ARCHI_BEXTRACTU((value),16,16))
#define UDMA_CPI_CAM_CFG_SIZE_ROWLEN_GETS(value)           (ARCHI_BEXTRACT((value),16,16))
#define UDMA_CPI_CAM_CFG_SIZE_ROWLEN_SET(value,field)      (ARCHI_BINSERT((value),(field),16,16))
#define UDMA_CPI_CAM_CFG_SIZE_ROWLEN(val)                  ((val) << 16)

#define UDMA_CPI_CAM_CFG_FILTER_B_COEFF_GET(value)         (ARCHI_BEXTRACTU((value),8,0))
#define UDMA_CPI_CAM_CFG_FILTER_B_COEFF_GETS(value)        (ARCHI_BEXTRACT((value),8,0))
#define UDMA_CPI_CAM_CFG_FILTER_B_COEFF_SET(value,field)   (ARCHI_BINSERT((value),(field),8,0))
#define UDMA_CPI_CAM_CFG_FILTER_B_COEFF(val)               ((val) << 0)

#define UDMA_CPI_CAM_CFG_FILTER_G_COEFF_GET(value)         (ARCHI_BEXTRACTU((value),8,8))
#define UDMA_CPI_CAM_CFG_FILTER_G_COEFF_GETS(value)        (ARCHI_BEXTRACT((value),8,8))
#define UDMA_CPI_CAM_CFG_FILTER_G_COEFF_SET(value,field)   (ARCHI_BINSERT((value),(field),8,8))
#define UDMA_CPI_CAM_CFG_FILTER_G_COEFF(val)               ((val) << 8)

#define UDMA_CPI_CAM_CFG_FILTER_R_COEFF_GET(value)         (ARCHI_BEXTRACTU((value),8,16))
#define UDMA_CPI_CAM_CFG_FILTER_R_COEFF_GETS(value)        (ARCHI_BEXTRACT((value),8,16))
#define UDMA_CPI_CAM_CFG_FILTER_R_COEFF_SET(value,field)   (ARCHI_BINSERT((value),(field),8,16))
#define UDMA_CPI_CAM_CFG_FILTER_R_COEFF(val)               ((val) << 16)

#define UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_GET(value) (ARCHI_BEXTRACTU((value),1,0))
#define UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_GETS(value) (ARCHI_BEXTRACT((value),1,0))
#define UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY_SET(value,field) (ARCHI_BINSERT((value),(field),1,0))
#define UDMA_CPI_CAM_VSYNC_POLARITY_VSYNC_POLARITY(val)    ((val) << 0)

#endif

#endif
