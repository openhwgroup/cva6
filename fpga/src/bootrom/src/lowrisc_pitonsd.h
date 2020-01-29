/* LowRISC_piton_sd register definitions
 *
 * Copyright 2019 University of Cambridge

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This header file is designed to also be usable outside Linux in which case
it is not covered by the GPL. When linked with the rest of Linux it is covered
by the GPL.
 *
 */

enum {
  _piton_sd_ADDR_SD     ,
  _piton_sd_ADDR_DMA    ,
  _piton_sd_BLKCNT      ,
  _piton_sd_REQ_RD      ,
  _piton_sd_REQ_WR      ,
  _piton_sd_IRQ_EN      ,
  _piton_sd_SYS_RST     };

enum {
  _piton_sd_ADDR_SD_F   ,
  _piton_sd_ADDR_DMA_F  ,
  _piton_sd_STATUS      ,
  _piton_sd_ERROR       ,
  _piton_sd_INIT_STATE  ,
  _piton_sd_COUNTER     ,
  _piton_sd_INIT_FSM    ,
  _piton_sd_TRAN_STATE  ,
  _piton_sd_TRAN_FSM    };

enum {
  _piton_sd_STATUS_REQ_RD       = (0x00000001),
  _piton_sd_STATUS_REQ_WR       = (0x00000002),
  _piton_sd_STATUS_IRQ_EN       = (0x00000004),
  _piton_sd_STATUS_SD_IRQ       = (0x00000008),
  _piton_sd_STATUS_REQ_RDY      = (0x00000010),
  _piton_sd_STATUS_INIT_DONE    = (0x00000020),
  _piton_sd_STATUS_HCXC         = (0x00000040),
  _piton_sd_STATUS_SD_DETECT    = (0x00000080)
  };

enum { _piton_sd_NUM_MINORS = 16 };
