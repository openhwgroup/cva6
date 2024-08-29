#ifndef __COREV_UVMT_H__
#define __COREV_UVMT_H__

/*
**
** Copyright 2021 OpenHW Group
** Copyright 2021 Silicon Labs
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
** CORE-V UVM Testbench (UVMT) defines
*******************************************************************************
*/

#define CV_VP_REGISTER_BASE          0x80800000

#define CV_VP_VIRTUAL_PRINTER_OFFSET        0x00000000
#define CV_VP_RANDOM_NUM_OFFSET             0x00000040
#define CV_VP_CYCLE_COUNTER_OFFSET          0x00000080
#define CV_VP_STATUS_FLAGS_OFFSET           0x000000c0
#define CV_VP_FENCEI_TAMPER_OFFSET          0x00000100
#define CV_VP_INTR_TIMER_OFFSET             0x00000140
#define CV_VP_DEBUG_CONTROL_OFFSET          0x00000180
#define CV_VP_OBI_SLV_RESP_OFFSET           0x000001c0
#define CV_VP_SIG_WRITER_OFFSET             0x00000200
#define CV_VP_OBI_ERR_AWAIT_GOAHEAD_OFFSET  0x00000240

#define CV_VP_CYCLE_COUNTER_BASE         (CV_VP_REGISTER_BASE + CV_VP_CYCLE_COUNTER_OFFSET)
#define CV_VP_DEBUG_CONTROL_BASE         (CV_VP_REGISTER_BASE + CV_VP_DEBUG_CONTROL_OFFSET)
#define CV_VP_FENCEI_TAMPER_BASE         (CV_VP_REGISTER_BASE + CV_VP_FENCEI_TAMPER_OFFSET)
#define CV_VP_INTR_TIMER_BASE            (CV_VP_REGISTER_BASE + CV_VP_INTR_TIMER_OFFSET)
#define CV_VP_OBI_ERR_AWAIT_GOAHEAD_BASE (CV_VP_REGISTER_BASE + CV_VP_OBI_ERR_AWAIT_GOAHEAD_OFFSET)
#define CV_VP_OBI_SLV_RESP_BASE          (CV_VP_REGISTER_BASE + CV_VP_OBI_SLV_RESP_OFFSET)
#define CV_VP_RANDOM_NUM_BASE            (CV_VP_REGISTER_BASE + CV_VP_RANDOM_NUM_OFFSET)
#define CV_VP_SIG_WRITER_BASE            (CV_VP_REGISTER_BASE + CV_VP_SIG_WRITER_OFFSET)
#define CV_VP_STATUS_FLAGS_BASE          (CV_VP_REGISTER_BASE + CV_VP_STATUS_FLAGS_OFFSET)
#define CV_VP_VIRTUAL_PRINTER_BASE       (CV_VP_REGISTER_BASE + CV_VP_VIRTUAL_PRINTER_OFFSET)

// --------------------------------------------------------------------------
// Registers inside the OBI_SLV_RESP VP
// --------------------------------------------------------------------------
#define CV_VP_OBI_SLV_RESP_I_ERR_ADDR_MIN    ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 4*0))
#define CV_VP_OBI_SLV_RESP_I_ERR_ADDR_MAX    ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 4*1))
#define CV_VP_OBI_SLV_RESP_I_ERR_VALID       ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 4*2))
#define CV_VP_OBI_SLV_RESP_I_EXOKAY_ADDR_MIN ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 4*3))
#define CV_VP_OBI_SLV_RESP_I_EXOKAY_ADDR_MAX ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 4*4))
#define CV_VP_OBI_SLV_RESP_I_EXOKAY_VALID    ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 4*5))

#define CV_VP_OBI_SLV_RESP_D_ERR_ADDR_MIN    ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 6*4 + 4*0))
#define CV_VP_OBI_SLV_RESP_D_ERR_ADDR_MAX    ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 6*4 + 4*1))
#define CV_VP_OBI_SLV_RESP_D_ERR_VALID       ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 6*4 + 4*2))
#define CV_VP_OBI_SLV_RESP_D_EXOKAY_ADDR_MIN ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 6*4 + 4*3))
#define CV_VP_OBI_SLV_RESP_D_EXOKAY_ADDR_MAX ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 6*4 + 4*4))
#define CV_VP_OBI_SLV_RESP_D_EXOKAY_VALID    ((volatile uint32_t*) (CV_VP_OBI_SLV_RESP_BASE + 6*4 + 4*5))

// API for Debug Control VP register
#define CV_VP_DEBUG_CONTROL_DBG_REQ(i)             ((i) << 31)
#define CV_VP_DEBUG_CONTROL_REQ_MODE(i)            ((i) << 30)
#define CV_VP_DEBUG_CONTROL_RAND_PULSE_DURATION(i) ((i) << 29)
#define CV_VP_DEBUG_CONTROL_PULSE_DURATION(i)      ((i) << 16)
#define CV_VP_DEBUG_CONTROL_RAND_START_DELAY(i)    ((i) << 15)
#define CV_VP_DEBUG_CONTROL_START_DELAY(i)         ((i) << 0)
#define CV_VP_DEBUG_CONTROL *((volatile uint32_t * volatile) (CV_VP_DEBUG_CONTROL_BASE))

#endif
