// Copyright 2024 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Yannick Casamatta - Thales
// Date: 09/01/2024


module cva6_rvfi_probes
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type rvfi_probes_t = logic
) (

    input logic        flush_i,
    input logic        issue_instr_ack_i,
    input logic        fetch_entry_valid_i,
    input logic [31:0] instruction_i,
    input logic        is_compressed_i,

    input logic [TRANS_ID_BITS-1:0] issue_pointer_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0][TRANS_ID_BITS-1:0] commit_pointer_i,

    input logic flush_unissued_instr_i,
    input logic decoded_instr_valid_i,
    input logic decoded_instr_ack_i,

    input riscv::xlen_t rs1_forwarding_i,
    input riscv::xlen_t rs2_forwarding_i,

    input scoreboard_entry_t [CVA6Cfg.NrCommitPorts-1:0] commit_instr_i,
    input exception_t ex_commit_i,
    input riscv::priv_lvl_t priv_lvl_i,

    input  lsu_ctrl_t                                                 lsu_ctrl_i,
    input  logic         [    CVA6Cfg.NrWbPorts-1:0][riscv::XLEN-1:0] wbdata_i,
    input  logic         [CVA6Cfg.NrCommitPorts-1:0]                  commit_ack_i,
    input  logic         [          riscv::PLEN-1:0]                  mem_paddr_i,
    input  logic                                                      debug_mode_i,
    input  logic         [CVA6Cfg.NrCommitPorts-1:0][riscv::XLEN-1:0] wdata_i,
    output rvfi_probes_t                                              rvfi_probes_o
);

  always_comb begin
    rvfi_probes_o = '0;

    rvfi_probes_o.flush = flush_i;
    rvfi_probes_o.issue_instr_ack = issue_instr_ack_i;
    rvfi_probes_o.fetch_entry_valid = fetch_entry_valid_i;
    rvfi_probes_o.instruction = instruction_i;
    rvfi_probes_o.is_compressed = is_compressed_i;

    rvfi_probes_o.issue_pointer = issue_pointer_i;
    rvfi_probes_o.commit_pointer = commit_pointer_i;

    rvfi_probes_o.flush_unissued_instr = flush_unissued_instr_i;
    rvfi_probes_o.decoded_instr_valid = decoded_instr_valid_i;
    rvfi_probes_o.decoded_instr_ack = decoded_instr_ack_i;

    rvfi_probes_o.rs1_forwarding = rs1_forwarding_i;
    rvfi_probes_o.rs2_forwarding = rs2_forwarding_i;

    rvfi_probes_o.commit_instr = commit_instr_i;
    rvfi_probes_o.ex_commit = ex_commit_i;
    rvfi_probes_o.priv_lvl = priv_lvl_i;

    rvfi_probes_o.lsu_ctrl = lsu_ctrl_i;
    rvfi_probes_o.wbdata = wbdata_i;
    rvfi_probes_o.commit_ack = commit_ack_i;
    rvfi_probes_o.mem_paddr = mem_paddr_i;
    rvfi_probes_o.debug_mode = debug_mode_i;
    rvfi_probes_o.wdata = wdata_i;

  end


endmodule
