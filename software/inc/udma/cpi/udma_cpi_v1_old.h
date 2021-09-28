/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
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

#ifndef __ARCHI_UDMA_UDMA_CPI_V1_H__
#define __ARCHI_UDMA_UDMA_CPI_V1_H__

// CAM custom registers offset definition
#define CAM_GLOB_OFFSET                  (0x00)
#define CAM_LL_OFFSET                    (0x04)
#define CAM_UR_OFFSET                    (0x08)
#define CAM_SIZE_OFFSET                  (0x0C)
#define CAM_FILTER_OFFSET                (0x10)

// CAM custom registers bitfields offset, mask, value definition
#define CAM_CFG_GLOB_FRAMEDROP_EN_OFFSET    0
#define CAM_CFG_GLOB_FRAMEDROP_EN_WIDTH     1
#define CAM_CFG_GLOB_FRAMEDROP_EN_MASK      (0x1 << CAM_CFG_GLOB_FRAMEDROP_EN_OFFSET)
#define CAM_CFG_GLOB_FRAMEDROP_EN_ENA     (1 << CAM_CFG_GLOB_FRAMEDROP_EN_OFFSET)
#define CAM_CFG_GLOB_FRAMEDROP_EN_DIS     (0 << CAM_CFG_GLOB_FRAMEDROP_EN_OFFSET)

#define CAM_CFG_GLOB_FRAMEDROP_VAL_OFFSET   1
#define CAM_CFG_GLOB_FRAMEDROP_VAL_WIDTH    6
#define CAM_CFG_GLOB_FRAMEDROP_VAL_MASK     (0x3f << CAM_CFG_GLOB_FRAMEDROP_VAL_OFFSET)
#define CAM_CFG_GLOB_FRAMEDROP_VAL(val)     (val << CAM_CFG_GLOB_FRAMEDROP_VAL_OFFSET)

#define CAM_CFG_GLOB_FRAMESLICE_EN_OFFSET   7
#define CAM_CFG_GLOB_FRAMESLICE_EN_WIDTH    1
#define CAM_CFG_GLOB_FRAMESLICE_EN_MASK   (0x1 << CAM_CFG_GLOB_FRAMESLICE_EN_OFFSET)
#define CAM_CFG_GLOB_FRAMESLICE_EN_ENA    (1 << CAM_CFG_GLOB_FRAMESLICE_EN_OFFSET)
#define CAM_CFG_GLOB_FRAMESLICE_EN_DIS    (0 << CAM_CFG_GLOB_FRAMESLICE_EN_OFFSET)

#define CAM_CFG_GLOB_FORMAT_OFFSET          8
#define CAM_CFG_GLOB_FORMAT_WIDTH         2
#define CAM_CFG_GLOB_FORMAT_MASK          (0x7 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_RGB565        (0 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_RGB555        (1 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_RGB444        (2 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_BYPASS_LITEND   (4 << CAM_CFG_GLOB_FORMAT_OFFSET)
#define CAM_CFG_GLOB_FORMAT_BYPASS_BIGEND   (5 << CAM_CFG_GLOB_FORMAT_OFFSET)

#define ARCHI_CAM_CFG_GLOB_FORMAT_RGB565          0
#define ARCHI_CAM_CFG_GLOB_FORMAT_RGB555          1
#define ARCHI_CAM_CFG_GLOB_FORMAT_RGB444          2
#define ARCHI_CAM_CFG_GLOB_FORMAT_BYPASS_LITEND   4
#define ARCHI_CAM_CFG_GLOB_FORMAT_BYPASS_BIGEND   5

#define CAM_CFG_GLOB_SHIFT_OFFSET           11
#define CAM_CFG_GLOB_SHIFT_WIDTH          4
#define CAM_CFG_GLOB_SHIFT_MASK           (0xf << CAM_CFG_GLOB_SHIFT_OFFSET)
#define CAM_CFG_GLOB_SHIFT(val)           (val << CAM_CFG_GLOB_SHIFT_OFFSET)

#define CAM_CFG_GLOB_EN_OFFSET              31
#define CAM_CFG_GLOB_EN_WIDTH               1
#define CAM_CFG_GLOB_EN_MASK              (0x1 << CAM_CFG_GLOB_EN_OFFSET)
#define CAM_CFG_GLOB_EN_ENA               (1 << CAM_CFG_GLOB_EN_OFFSET)
#define CAM_CFG_GLOB_EN_DIS               (0 << CAM_CFG_GLOB_EN_OFFSET)

#define CAM_CFG_LL_FRAMESLICE_LLX_OFFSET    0
#define CAM_CFG_LL_FRAMESLICE_LLX_WIDTH   16
#define CAM_CFG_LL_FRAMESLICE_LLX_MASK    (0xffff << CAM_CFG_LL_FRAMESLICE_LLX_OFFSET)
#define CAM_CFG_LL_FRAMESLICE_LLX(val)    (val << CAM_CFG_LL_FRAMESLICE_LLX_OFFSET)

#define CAM_CFG_LL_FRAMESLICE_LLY_OFFSET    16
#define CAM_CFG_LL_FRAMESLICE_LLY_WIDTH   16
#define CAM_CFG_LL_FRAMESLICE_LLY_MASK    (0xffff << CAM_CFG_LL_FRAMESLICE_LLY_OFFSET)
#define CAM_CFG_LL_FRAMESLICE_LLY(val)    (val << CAM_CFG_LL_FRAMESLICE_LLY_OFFSET)

#define CAM_CFG_UR_FRAMESLICE_URX_OFFSET    0
#define CAM_CFG_UR_FRAMESLICE_URX_WIDTH   16
#define CAM_CFG_UR_FRAMESLICE_URX_MASK    (0xffff << CAM_CFG_UR_FRAMESLICE_URX_OFFSET)
#define CAM_CFG_UR_FRAMESLICE_URX(val)    (val << CAM_CFG_UR_FRAMESLICE_URX_OFFSET)

#define CAM_CFG_UR_FRAMESLICE_URY_OFFSET    16
#define CAM_CFG_UR_FRAMESLICE_URY_WIDTH   16
#define CAM_CFG_UR_FRAMESLICE_URY_MASK    (0xffff << CAM_CFG_UR_FRAMESLICE_URY_OFFSET)
#define CAM_CFG_UR_FRAMESLICE_URY(val)    (val << CAM_CFG_UR_FRAMESLICE_URY_OFFSET)

#define CAM_CFG_SIZE_ROWLEN_OFFSET      16
#define CAM_CFG_SIZE_ROWLEN_WIDTH     16
#define CAM_CFG_SIZE_ROWLEN_MASK    (0xffff << CAM_CFG_SIZE_ROWLEN_OFFSET)
#define CAM_CFG_SIZE_ROWLEN(val)    ((val - 1) << CAM_CFG_SIZE_ROWLEN_OFFSET)

#define CAM_CFG_FILTER_B_COEFF_OFFSET     0
#define CAM_CFG_FILTER_B_COEFF_WIDTH    8
#define CAM_CFG_FILTER_B_COEFF_MASK     (0xff << CAM_CFG_FILTER_B_COEFF_OFFSET)
#define CAM_CFG_FILTER_B_COEFF(val)     (val << CAM_CFG_FILTER_B_COEFF_OFFSET)

#define CAM_CFG_FILTER_G_COEFF_OFFSET     8
#define CAM_CFG_FILTER_G_COEFF_WIDTH    8
#define CAM_CFG_FILTER_G_COEFF_MASK     (0xff << CAM_CFG_FILTER_G_COEFF_OFFSET)
#define CAM_CFG_FILTER_G_COEFF(val)     (val << CAM_CFG_FILTER_G_COEFF_OFFSET)

#define CAM_CFG_FILTER_R_COEFF_OFFSET     16
#define CAM_CFG_FILTER_R_COEFF_WIDTH    8
#define CAM_CFG_FILTER_R_COEFF_MASK     (0xff << CAM_CFG_FILTER_R_COEFF_OFFSET)
#define CAM_CFG_FILTER_R_COEFF(val)     (val << CAM_CFG_FILTER_R_COEFF_OFFSET)

// TODO Add enum definitions of CAM register bitfields

///////////////////////////////////////////////////
// TODO Obsolete : to be removed cause deprecated
#define CAM_CFG_GLOB_FRAMEDROP_EN_BIT   0
#define CAM_CFG_GLOB_FRAMEDROP_VAL_BIT  1
#define CAM_CFG_GLOB_FRAMEDROP_VAL_SIZE 6
#define CAM_CFG_GLOB_FRAMESLICE_EN_BIT  7
#define CAM_CFG_GLOB_FORMAT_BIT         8
#define CAM_CFG_GLOB_FORMAT_SIZE        3
#define CAM_CFG_GLOB_SHIFT_BIT          11
#define CAM_CFG_GLOB_SHIFT_SIZE         4
#define CAM_CFG_GLOB_EN_BIT             31

//+ #define CAM_CFG_GLOB_FORMAT_RGB565      0
//+ #define CAM_CFG_GLOB_FORMAT_RGB555      1
//+ #define CAM_CFG_GLOB_FORMAT_RGB444      2
//+ #define CAM_CFG_GLOB_FORMAT_BYPASS      3

#define CAM_CFG_LL_FRAMESLICE_LLX_BIT   0
#define CAM_CFG_LL_FRAMESLICE_LLX_SIZE  16
#define CAM_CFG_LL_FRAMESLICE_LLY_BIT   16
#define CAM_CFG_LL_FRAMESLICE_LLY_SIZE  16

#define CAM_CFG_UR_FRAMESLICE_URX_BIT   0
#define CAM_CFG_UR_FRAMESLICE_URX_SIZE  16
#define CAM_CFG_UR_FRAMESLICE_URY_BIT   16
#define CAM_CFG_UR_FRAMESLICE_URY_SIZE  16

#define CAM_CFG_SIZE_ROWLEN_BIT  16
#define CAM_CFG_SIZE_ROWLEN_SIZE 16

#define CAM_CFG_FILTER_B_COEFF_BIT  0
#define CAM_CFG_FILTER_B_COEFF_SIZE 8
#define CAM_CFG_FILTER_G_COEFF_BIT  8
#define CAM_CFG_FILTER_G_COEFF_SIZE 8
#define CAM_CFG_FILTER_R_COEFF_BIT  16
#define CAM_CFG_FILTER_R_COEFF_SIZE 8
///////////////////////////////////////////////////

#endif