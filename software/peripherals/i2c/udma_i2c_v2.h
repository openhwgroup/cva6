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

#ifndef __ARCHI_UDMA_UDMA_I2C_V2_H__
#define __ARCHI_UDMA_UDMA_I2C_V2_H__

// I2C command IDS definition
#define I2C_CMD_OFFSET       4
#define I2C_CMD_START                    (0x0 << I2C_CMD_OFFSET)
#define I2C_CMD_STOP                     (0x2 << I2C_CMD_OFFSET)
#define I2C_CMD_RD_ACK                   (0x4 << I2C_CMD_OFFSET)
#define I2C_CMD_RD_NACK                  (0x6 << I2C_CMD_OFFSET)
#define I2C_CMD_WR                       (0x8 << I2C_CMD_OFFSET)
#define I2C_CMD_WAIT                     (0xA << I2C_CMD_OFFSET)
#define I2C_CMD_RPT                      (0xC << I2C_CMD_OFFSET)
#define I2C_CMD_CFG                      (0xE << I2C_CMD_OFFSET)
#define I2C_CMD_WAIT_EV                  (0x1 << I2C_CMD_OFFSET)

#endif