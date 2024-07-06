// Copyright 2022 Silicon Laboratories Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you
// may not use this file except in compliance with the License, or, at your
// option, the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.


enum {
  EXC_CAUSE_INSTR_ACC_FAULT       = 1,
  EXC_CAUSE_ILLEGAL_INSTR         = 2,
  EXC_CAUSE_BREAKPOINT            = 3,
  EXC_CAUSE_LOAD_ACC_FAULT        = 5,
  EXC_CAUSE_STORE_ACC_FAULT       = 7,
  EXC_CAUSE_ENV_CALL_U            = 8,
  EXC_CAUSE_ENV_CALL_M            = 11,
  EXC_CAUSE_INSTR_BUS_FAULT       = 24,
  EXC_CAUSE_INSTR_INTEGRITY_FAULT = 25,
};

typedef enum {
  PMPMODE_OFF   = 0,
  PMPMODE_TOR   = 1,
  PMPMODE_NA4   = 2,
  PMPMODE_NAPOT = 3
} pmp_mode_t;

// Verbosity levels (Akin to the uvm verbosity concept)
typedef enum {
  V_OFF    = 0,
  V_LOW    = 1,
  V_MEDIUM = 2,
  V_HIGH   = 3,
  V_DEBUG  = 4
} verbosity_t;

// Matches funct3 values for CSR instructions
typedef enum {
  CSRRW  = 1,
  CSRRS  = 2,
  CSRRC  = 3,
  CSRRWI = 5,
  CSRRSI = 6,
  CSRRCI = 7
} csr_instr_access_t;

typedef union {
  struct {
    volatile uint32_t opcode   : 7;
    volatile uint32_t rd       : 5;
    volatile uint32_t funct3   : 3;
    volatile uint32_t rs1_uimm : 5;
    volatile uint32_t csr      : 12;
  } volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) csr_instr_t;

typedef union {
  struct {
    volatile uint32_t  load     : 1;
    volatile uint32_t  store    : 1;
    volatile uint32_t  execute  : 1;
    volatile uint32_t  u        : 1;
    volatile uint32_t  s        : 1;
    volatile uint32_t  res_5_5  : 1;
    volatile uint32_t  m        : 1;
    volatile uint32_t  match    : 4;
    volatile uint32_t  chain    : 1;
    volatile uint32_t  action   : 4;
    volatile uint32_t  size     : 4;
    volatile uint32_t  timing   : 1;
    volatile uint32_t  select   : 1;
    volatile uint32_t  hit      : 1;
    volatile uint32_t  vu       : 1;
    volatile uint32_t  vs       : 1;
    volatile uint32_t  res_26_25: 2;
    volatile uint32_t  dmode    : 1;
    volatile uint32_t  type     : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) mcontrol6_t;

typedef union {
  struct {
    volatile uint32_t uie   : 1;  //     0
    volatile uint32_t sie   : 1;  //     1
    volatile uint32_t wpri  : 1;  //     2
    volatile uint32_t mie   : 1;  //     3
    volatile uint32_t upie  : 1;  //     4
    volatile uint32_t spie  : 1;  //     5
    volatile uint32_t wpri0 : 1;  //     6
    volatile uint32_t mpie  : 1;  //     7
    volatile uint32_t spp   : 1;  //     8
    volatile uint32_t wpri1 : 2;  // 10: 9
    volatile uint32_t mpp   : 2;  // 12:11
    volatile uint32_t fs    : 2;  // 14:13
    volatile uint32_t xs    : 2;  // 16:15
    volatile uint32_t mprv  : 1;  //    17
    volatile uint32_t sum   : 1;  //    18
    volatile uint32_t mxr   : 1;  //    19
    volatile uint32_t tvm   : 1;  //    20
    volatile uint32_t tw    : 1;  //    21
    volatile uint32_t tsr   : 1;  //    22
    volatile uint32_t wpri3 : 8;  // 30:23
    volatile uint32_t sd    : 1;  //    31
  } volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) mstatus_t;

typedef union {
  struct {
    volatile uint32_t mml           : 1;
    volatile uint32_t mmwp          : 1;
    volatile uint32_t rlb           : 1;
    volatile uint32_t reserved_31_3 : 29;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 32;
} __attribute__((packed)) mseccfg_t;

typedef union {
  struct {
    volatile uint32_t reserved_1_0  : 2;
    volatile uint32_t jvt_access    : 1;
    volatile uint32_t reserved_31_3 : 29;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 32;
} __attribute__((packed)) mstateen0_t;

typedef union {
  struct {
    volatile uint32_t r            : 1;
    volatile uint32_t w            : 1;
    volatile uint32_t x            : 1;
    volatile uint32_t a            : 2;
    volatile uint32_t reserved_6_5 : 2;
    volatile uint32_t l            : 1;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 8;
} __attribute__((packed)) pmpsubcfg_t;

typedef union {
  struct {
    volatile uint32_t cfg : 8;
  } __attribute__((packed)) volatile reg_idx[4];
  volatile uint32_t raw : 32;
} __attribute__((packed)) pmpcfg_t;

typedef union {
  struct {
    volatile uint32_t mode : 6;
    volatile uint32_t base : 26;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 32;
} __attribute__((packed)) jvt_t;

typedef union {
  struct {
    volatile uint32_t exccode   : 12;
    volatile uint32_t res_30_12 : 19;
    volatile uint32_t interrupt : 1;
  } __attribute__((packed)) volatile clint;
  struct {
    volatile uint32_t exccode    : 12;
    volatile uint32_t res_15_12  : 4;
    volatile uint32_t mpil       : 8;
    volatile uint32_t res_26_24  : 3;
    volatile uint32_t mpie       : 1;
    volatile uint32_t mpp        : 2;
    volatile uint32_t minhv      : 1;
    volatile uint32_t interrupt  : 1;
  } __attribute__((packed)) volatile clic;
  volatile uint32_t raw : 32;
} __attribute__((packed)) mcause_t;
