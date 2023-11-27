// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Authors: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//          Nils Wistoff <nwistoff@iis.ee.ethz.ch>

// Package defining the accelerator interface as used by Ara + CVA6

package acc_pkg;

  // ----------------------
  // Accelerator Interface
  // ----------------------

  typedef struct packed {
    logic                                 req_valid;
    logic                                 resp_ready;
    riscv::instruction_t                  insn;
    logic [CVA6Cfg.XLEN-1:0]                         rs1;
    logic [CVA6Cfg.XLEN-1:0]                         rs2;
    fpnew_pkg::roundmode_e                frm;
    logic [ariane_pkg::TRANS_ID_BITS-1:0] trans_id;
    logic                                 store_pending;
    // Invalidation interface
    logic                                 acc_cons_en;
    logic                                 inval_ready;
  } accelerator_req_t;

  typedef struct packed {
    logic                                 req_ready;
    logic                                 resp_valid;
    logic [CVA6Cfg.XLEN-1:0]                         result;
    logic [ariane_pkg::TRANS_ID_BITS-1:0] trans_id;
    logic                                 error;
    // Metadata
    logic                                 store_pending;
    logic                                 store_complete;
    logic                                 load_complete;
    logic [4:0]                           fflags;
    logic                                 fflags_valid;
    // Invalidation interface
    logic                                 inval_valid;
    logic [63:0]                          inval_addr;
  } accelerator_resp_t;

endpackage
