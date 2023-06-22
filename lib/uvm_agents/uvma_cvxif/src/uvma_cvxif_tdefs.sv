// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_TDEFS_SV__
`define __UVMA_CVXIF_TDEFS_SV__


   localparam X_DATAWIDTH  = cvxif_pkg::X_DATAWIDTH;
   localparam X_ID_WIDTH   = cvxif_pkg::X_ID_WIDTH;
   localparam X_RFW_WIDTH  = cvxif_pkg::X_RFW_WIDTH;
   localparam X_NUM_RS     = cvxif_pkg::X_NUM_RS;
   localparam X_RFR_WIDTH  = cvxif_pkg::X_RFR_WIDTH;

typedef struct packed {
   logic    accept;
   logic    writeback;
   logic    dualwrite;
   logic    dualread;
   logic    loadstore;
   logic    exc;
} issue_resp_t;

typedef struct packed {
   logic  [X_ID_WIDTH-1:0]   id;
   logic  [X_DATAWIDTH-1:0]  data;
   logic  [4:0]              rd;
   logic  [X_RFW_WIDTH/riscv::XLEN-1:0]  we;
   logic                     exc;
   logic  [5:0]              exccode;
} result_t ;

typedef enum logic[1:0] {
   PRIV_LVL_M = 2'b11,
   PRIV_LVL_S = 2'b01,
   PRIV_LVL_U = 2'b00
  } priv_lvl_t;

typedef struct packed {
   logic  [31:0]                          instr;
   logic  [X_ID_WIDTH-1:0]                id;
   priv_lvl_t                             mode;
   logic  [X_NUM_RS-1:0][X_RFR_WIDTH-1:0] rs;
   logic  [X_NUM_RS-1:0]                  rs_valid;
} x_issue_req;

typedef struct packed {
   logic  [X_ID_WIDTH-1:0]      id;
   logic                        commit_kill;
} x_commit;

typedef enum {
   UVMA_CVXIF_ISSUE_READY_FIX,
   UVMA_CVXIF_ISSUE_READY_RANDOMIZED
} uvma_cvxif_ready_mode_enum;

typedef struct packed {
   logic                     result_valid;
   logic                     result_ready;
   logic  [X_ID_WIDTH-1:0]   id;
   logic  [X_DATAWIDTH-1:0]  data;
   logic  [4:0]              rd;
   logic  [X_RFW_WIDTH/riscv::XLEN-1:0]  we;
   logic                     exc;
   logic  [5:0]              exccode;
   int                       rnd_delay;
  } drv_result;

`endif //__UVMA_CVXIF_TDEFS_SV__
