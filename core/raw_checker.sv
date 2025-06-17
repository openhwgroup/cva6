// Copyright 2024 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 0.51 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Junheng Zheng - Thales

module raw_checker
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // Register source of the instruction to check RAW dependancies - SCOREBOARD 
    input logic [REG_ADDR_SIZE-1:0] rs_i,
    // Type of register source (FPR or GPR) - SCOREBOARD
    input logic rs_fpr_i,
    // Registers of destination of the instructions already issued in the scoreboard - SCOREBOARD 
    input logic [CVA6Cfg.NR_SB_ENTRIES-1:0][REG_ADDR_SIZE-1:0] rd_i,
    // Type of registers of destination (FPR or GPR) - SCOREBOARD
    input logic [CVA6Cfg.NR_SB_ENTRIES-1:0] rd_fpr_i,
    // Instructions in the scoreboard are still issued - SCOREBOARD
    input logic [CVA6Cfg.NR_SB_ENTRIES-1:0] still_issued_i,
    // Issue pointer - SCOREBOARD
    input logic [CVA6Cfg.TRANS_ID_BITS-1:0] issue_pointer_i,

    // Index in the scoreboard of the most recent RAW dependancy - SCOREBOARD
    output logic [CVA6Cfg.TRANS_ID_BITS-1:0] idx_o,
    // Indicates if there is a RAW dependancy - SCOREBOARD
    output logic valid_o
);

  logic [CVA6Cfg.NR_SB_ENTRIES-1:0] same_rd_as_rs;

  logic [CVA6Cfg.NR_SB_ENTRIES-1:0] same_rd_as_rs_before;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] last_before_idx;

  logic [CVA6Cfg.NR_SB_ENTRIES-1:0] same_rd_as_rs_after;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] last_after_idx;

  logic                             rs_is_gpr0;

  for (genvar i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
    assign same_rd_as_rs[i] = (rs_fpr_i == rd_fpr_i[i]) && (rs_i == rd_i[i]) && still_issued_i[i];
    assign same_rd_as_rs_before[i] = (i < issue_pointer_i) && same_rd_as_rs[i];
    assign same_rd_as_rs_after[i] = (i >= issue_pointer_i) && same_rd_as_rs[i];
  end

  always_comb begin
    last_before_idx = '0;
    last_after_idx  = '0;

    for (int unsigned i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
      if (same_rd_as_rs_before[i]) begin
        last_before_idx = i;
      end
      if (same_rd_as_rs_after[i]) begin
        last_after_idx = i;
      end
    end
  end

  assign idx_o = |same_rd_as_rs_before ? last_before_idx : last_after_idx;

  assign rs_is_gpr0 = (rs_i == '0) && !rs_fpr_i;
  assign valid_o = |same_rd_as_rs && !rs_is_gpr0;

endmodule
