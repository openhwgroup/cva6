// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVMA_OBI_MEMORY_TDEFS_SV__
`define __UVMA_OBI_MEMORY_TDEFS_SV__


// Logic vectors
typedef logic [(`UVMA_OBI_MEMORY_AUSER_MAX_WIDTH   -1):0]  uvma_obi_memory_auser_l_t  ;
typedef logic [(`UVMA_OBI_MEMORY_WUSER_MAX_WIDTH   -1):0]  uvma_obi_memory_wuser_l_t  ;
typedef logic [(`UVMA_OBI_MEMORY_RUSER_MAX_WIDTH   -1):0]  uvma_obi_memory_ruser_l_t  ;
typedef logic [(`UVMA_OBI_MEMORY_ADDR_MAX_WIDTH    -1):0]  uvma_obi_memory_addr_l_t   ;
typedef logic [(`UVMA_OBI_MEMORY_DATA_MAX_WIDTH    -1):0]  uvma_obi_memory_data_l_t   ;
typedef logic [((`UVMA_OBI_MEMORY_DATA_MAX_WIDTH/8)-1):0]  uvma_obi_memory_be_l_t     ;
typedef logic [(`UVMA_OBI_MEMORY_ID_MAX_WIDTH      -1):0]  uvma_obi_memory_id_l_t     ;
typedef logic                                              uvma_obi_memory_err_l_t    ;
typedef logic                                              uvma_obi_memory_exokay_l_t ;
typedef logic [5:0]                                        uvma_obi_memory_atop_l_t   ;
typedef logic [1:0]                                        uvma_obi_memory_memtype_l_t;
typedef logic [2:0]                                        uvma_obi_memory_prot_l_t   ;
typedef logic [(`UVMA_OBI_MEMORY_ACHK_MAX_WIDTH    -1):0]  uvma_obi_memory_achk_l_t   ;
typedef logic [(`UVMA_OBI_MEMORY_RCHK_MAX_WIDTH    -1):0]  uvma_obi_memory_rchk_l_t   ;

// Bit vectors
typedef bit [(`UVMA_OBI_MEMORY_AUSER_MAX_WIDTH   -1):0]  uvma_obi_memory_auser_b_t  ;
typedef bit [(`UVMA_OBI_MEMORY_WUSER_MAX_WIDTH   -1):0]  uvma_obi_memory_wuser_b_t  ;
typedef bit [(`UVMA_OBI_MEMORY_RUSER_MAX_WIDTH   -1):0]  uvma_obi_memory_ruser_b_t  ;
typedef bit [(`UVMA_OBI_MEMORY_ADDR_MAX_WIDTH    -1):0]  uvma_obi_memory_addr_b_t   ;
typedef bit [(`UVMA_OBI_MEMORY_DATA_MAX_WIDTH    -1):0]  uvma_obi_memory_data_b_t   ;
typedef bit [((`UVMA_OBI_MEMORY_DATA_MAX_WIDTH/8)-1):0]  uvma_obi_memory_be_b_t     ;
typedef bit [(`UVMA_OBI_MEMORY_ID_MAX_WIDTH      -1):0]  uvma_obi_memory_id_b_t     ;
typedef bit                                              uvma_obi_memory_err_b_t    ;
typedef bit                                              uvma_obi_memory_exokay_b_t ;
typedef bit [5:0]                                        uvma_obi_memory_atop_b_t   ;
typedef bit [1:0]                                        uvma_obi_memory_memtype_b_t;
typedef bit [2:0]                                        uvma_obi_memory_prot_b_t   ;
typedef bit [(`UVMA_OBI_MEMORY_ACHK_MAX_WIDTH    -1):0]  uvma_obi_memory_achk_b_t   ;
typedef bit [(`UVMA_OBI_MEMORY_RCHK_MAX_WIDTH    -1):0]  uvma_obi_memory_rchk_b_t   ;


typedef enum {
   UVMA_OBI_MEMORY_VERSION_1P1,
   UVMA_OBI_MEMORY_VERSION_1P2
} uvma_obi_memory_version_enum;

typedef enum {
   UVMA_OBI_MEMORY_MODE_MSTR,
   UVMA_OBI_MEMORY_MODE_SLV
} uvma_obi_memory_mode_enum;

typedef enum {
   UVMA_OBI_MEMORY_RESET_STATE_PRE_RESET ,
   UVMA_OBI_MEMORY_RESET_STATE_IN_RESET  ,
   UVMA_OBI_MEMORY_RESET_STATE_POST_RESET
} uvma_obi_memory_reset_state_enum;

typedef enum {
   UVMA_OBI_MEMORY_DRV_IDLE_SAME  ,
   UVMA_OBI_MEMORY_DRV_IDLE_ZEROS ,
   UVMA_OBI_MEMORY_DRV_IDLE_RANDOM,
   UVMA_OBI_MEMORY_DRV_IDLE_X     ,
   UVMA_OBI_MEMORY_DRV_IDLE_Z
} uvma_obi_memory_drv_idle_enum;

typedef enum {
   UVMA_OBI_MEMORY_PHASE_INACTIVE,
   UVMA_OBI_MEMORY_PHASE_SETUP   ,
   UVMA_OBI_MEMORY_PHASE_ACCESS
} uvma_obi_memory_phases_enum;

typedef enum {
   UVMA_OBI_MEMORY_ACCESS_READ ,
   UVMA_OBI_MEMORY_ACCESS_WRITE
} uvma_obi_memory_access_type_enum;

typedef enum {
   UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_CONSTANT      ,
   UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_FIXED_LATENCY ,
   UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_RANDOM_LATENCY
} uvma_obi_memory_drv_slv_gnt_mode_enum;

typedef enum {
   UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_CONSTANT      ,
   UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_FIXED_LATENCY ,
   UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_RANDOM_LATENCY
} uvma_obi_memory_drv_slv_rvalid_mode_enum;

typedef enum {
   UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_OK,
   UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_RANDOM
} uvma_obi_memory_drv_slv_err_mode_enum;

typedef enum {
   UVMA_OBI_MEMORY_DRV_SLV_EXOKAY_MODE_SUCCESS,
   UVMA_OBI_MEMORY_DRV_SLV_EXOKAY_MODE_RANDOM
} uvma_obi_memory_drv_slv_exokay_mode_enum;

`endif // __UVMA_OBI_MEMORY_TDEFS_SV__
