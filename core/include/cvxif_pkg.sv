// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Guillaume CHAUVON (guillaume.chauvon@thalesgroup.com)

// Package for the CoreV-X-Interface for the CVA6

package cvxif_pkg;

  localparam int unsigned X_NUM_RS               = 2;  // Number of register file read ports that can be used by the eXtension interface
  localparam int unsigned X_ID_WIDTH             = 4;  // Width of ID field.
  localparam int unsigned X_RFR_WIDTH            = 32; // Register file read access width for the eXtension interface
  localparam int unsigned X_RFW_WIDTH            = 32; // Register file write access width for the eXtension interface
  localparam int unsigned X_NUM_HARTS            = 1;  // Number of harts (hardware threads) associated with the interface
  localparam int unsigned X_HARTID_WIDTH         = 32;  // Width of ``hartid`` signals.
  localparam logic [25:0] X_MISA                 = '0; // MISA extensions implemented on the eXtension interface
  localparam int unsigned X_DUALREAD             = 0;  // Is dual read supported? 0: No, 1: Yes, for ``rs1``, 2: Yes, for ``rs1`` - ``rs2``, 3: Yes, for ``rs1`` - ``rs3``
  localparam int unsigned X_DUALWRITE            = 0;  // Is dual write supported? 0: No, 1: Yes.
  localparam int unsigned X_ISSUE_REGISTER_SPLIT = 0;  // Does the interface pipeline register interface? 0: No, 1: Yes.

  typedef logic [X_NUM_RS+X_DUALREAD-1:0] readregflags_t;
  typedef logic [X_DUALWRITE:0] writeregflags_t;
  typedef logic [X_ID_WIDTH-1:0] id_t;
  typedef logic [X_HARTID_WIDTH-1:0] hartid_t;

  typedef struct packed {
    logic [15:0] instr;  // Offloaded compressed instruction
    hartid_t hartid;  // Identification of the hart offloading the instruction
  } x_compressed_req_t;

  typedef struct packed {
    logic [31:0] instr;  // Uncompressed instruction
    logic accept;  // Is the offloaded compressed instruction (id) accepted by the coprocessor?
  } x_compressed_resp_t;

  typedef struct packed {
    logic [31:0] instr;  // Offloaded instruction
    hartid_t hartid;  // Identification of the hart offloading the instruction
    id_t id;  // Identification of the offloaded instruction
  } x_issue_req_t;

  typedef struct packed {
    logic accept;  // Is the offloaded instruction (id) accepted by the coprocessor?
    writeregflags_t writeback;  // Will the coprocessor perform a writeback in the core to rd?
    readregflags_t register_read;   // Will the coprocessor perform require specific registers to be read?
  } x_issue_resp_t;

  typedef struct packed {
    hartid_t hartid;  // Identification of the hart offloading the instruction
    id_t id;  // Identification of the offloaded instruction
    /* verilator lint_off UNPACKED */
    logic [X_NUM_RS-1:0][X_RFR_WIDTH-1:0] rs;  // Register file source operands for the offloaded instruction.
    readregflags_t rs_valid; // Validity of the register file source operand(s).
  } x_register_t;

  typedef struct packed {
    hartid_t hartid;  // Identification of the hart offloading the instruction
    id_t id;  // Identification of the offloaded instruction
    logic commit_kill;  // Shall an offloaded instruction be killed?
  } x_commit_t;

  typedef struct packed {
    hartid_t hartid;  // Identification of the hart offloading the instruction
    id_t id;  // Identification of the offloaded instruction
    logic [X_RFW_WIDTH     -1:0] data;  // Register file write data value(s)
    logic [4:0] rd;  // Register file destination address(es)
    writeregflags_t we;  // Register file write enable(s)
  } x_result_t;

  typedef struct packed {
    logic              compressed_valid;
    x_compressed_req_t compressed_req;
    logic              issue_valid;
    x_issue_req_t      issue_req;
    logic              register_valid;
    x_register_t       register;
    logic              commit_valid;
    x_commit_t         commit;
    logic              result_ready;
  } cvxif_req_t;

  typedef struct packed {
    logic               compressed_ready;
    x_compressed_resp_t compressed_resp;
    logic               issue_ready;
    x_issue_resp_t      issue_resp;
    logic               register_ready;
    logic               result_valid;
    x_result_t          result;
  } cvxif_resp_t;

endpackage
