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
  logic                             last_before_valid;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] last_before_idx;

  logic [CVA6Cfg.NR_SB_ENTRIES-1:0] same_rd_as_rs_after;
  logic                             last_after_valid;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] last_after_idx;

  logic                             valid;
  logic                             rs_is_gpr0;

  for (genvar i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
    assign same_rd_as_rs[i] = (rs_fpr_i == rd_fpr_i[i]) && (rs_i == rd_i[i]) && still_issued_i[i];
    assign same_rd_as_rs_before[i] = (i < issue_pointer_i) && same_rd_as_rs[i];
    assign same_rd_as_rs_after[i] = (i >= issue_pointer_i) && same_rd_as_rs[i];
  end

  //Last finders
  // for instructions < instruction pointer
  rr_arb_tree #(
      .NumIn(CVA6Cfg.NR_SB_ENTRIES),
      .DataWidth(1),
      .ExtPrio(1'b1),
      .AxiVldRdy(1'b1)
  ) i_last_finder_before (
      .clk_i  (clk_i),
      .rst_ni (rst_ni),
      .flush_i(1'b0),
      .rr_i   ({$clog2(CVA6Cfg.NR_SB_ENTRIES){1'b1}}), // Highest index has highest prio.
      .req_i  (same_rd_as_rs_before),
      .gnt_o  (),
      .data_i ('0),
      .gnt_i  (1'b1),
      .req_o  (last_before_valid),
      .data_o (),
      .idx_o  (last_before_idx)
  );

  // for instructions >= instruction pointer
  rr_arb_tree #(
      .NumIn(CVA6Cfg.NR_SB_ENTRIES),
      .DataWidth(1),
      .ExtPrio(1'b1),
      .AxiVldRdy(1'b1)
  ) i_last_finder_after (
      .clk_i  (clk_i),
      .rst_ni (rst_ni),
      .flush_i(1'b0),
      .rr_i   ({$clog2(CVA6Cfg.NR_SB_ENTRIES){1'b1}}), // Highest index has highest prio.
      .req_i  (same_rd_as_rs_after),
      .gnt_o  (),
      .data_i ('0),
      .gnt_i  (1'b1),
      .req_o  (last_after_valid),
      .data_o (),
      .idx_o  (last_after_idx)
  );

  // take the minimum of the last indexes
  rr_arb_tree #(
      .NumIn(2),
      .DataWidth(CVA6Cfg.TRANS_ID_BITS),
      .ExtPrio(1'b1),
      .AxiVldRdy(1'b1)
  ) min_finder (
      .clk_i  (clk_i),
      .rst_ni (rst_ni),
      .flush_i(1'b0),
      .rr_i   ('0), // Lowest index has highest prio.
      .req_i  ({last_after_valid,last_before_valid}),
      .gnt_o  (),
      .data_i ({last_after_idx,last_before_idx}),
      .gnt_i  (1'b1),
      .req_o  (valid),
      .data_o (idx_o),
      .idx_o  ()
  );

  assign rs_is_gpr0 = (rs_i == '0) && !rs_fpr_i;
  assign valid_o = valid && !rs_is_gpr0;

endmodule
