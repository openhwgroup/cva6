// Copyright 2020 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.com)

package ariane_rvfi_pkg;

  localparam NRET = 1;
  localparam ILEN = 32;

  typedef struct packed {
    logic [NRET-1:0]                 valid;
    logic [NRET*64-1:0]              order;
    logic [NRET*ILEN-1:0]            insn;
    logic [NRET-1:0]                 trap;
    logic [NRET*riscv::XLEN-1:0]     cause;
    logic [NRET-1:0]                 halt;
    logic [NRET-1:0]                 intr;
    logic [NRET*2-1:0]               mode;
    logic [NRET*2-1:0]               ixl;
    logic [NRET*5-1:0]               rs1_addr;
    logic [NRET*5-1:0]               rs2_addr;
    logic [NRET*riscv::XLEN-1:0]     rs1_rdata;
    logic [NRET*riscv::XLEN-1:0]     rs2_rdata;
    logic [NRET*5-1:0]               rd_addr;
    logic [NRET*riscv::XLEN-1:0]     rd_wdata;

    logic [NRET*riscv::XLEN-1:0]     pc_rdata;
    logic [NRET*riscv::XLEN-1:0]     pc_wdata;

    logic [NRET*riscv::XLEN-1:0]     mem_addr;
    logic [NRET*(riscv::XLEN/8)-1:0] mem_rmask;
    logic [NRET*(riscv::XLEN/8)-1:0] mem_wmask;
    logic [NRET*riscv::XLEN-1:0]     mem_rdata;
    logic [NRET*riscv::XLEN-1:0]     mem_wdata;
  } rvfi_instr_t;

  typedef rvfi_instr_t [ariane_pkg::NR_COMMIT_PORTS-1:0] rvfi_port_t;

endpackage
