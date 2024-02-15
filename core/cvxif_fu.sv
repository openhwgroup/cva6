// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Guillaume CHAUVON (guillaume.chauvon@thalesgroup.com)

// Functional Unit for the logic of the CoreV-X-Interface


module cvxif_fu
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type exception_t = logic,
    parameter type fu_data_t = logic
) (
    // Subsystem Clock - SUBSYSTEM
    input  logic                                               clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input  logic                                               rst_ni,
    // FU data needed to execute instruction - ISSUE_STAGE
    input  fu_data_t                                           fu_data_i,
    // Current privilege mode - CSR_REGFILE
    input  riscv::priv_lvl_t                                   priv_lvl_i,
    // CVXIF instruction is valid - ISSUE_STAGE
    input  logic                                               x_valid_i,
    // CVXIF is ready - ISSUE_STAGE
    output logic                                               x_ready_o,
    // Offloaded instruction - ISSUE_STAGE
    input  logic                   [                     31:0] x_off_instr_i,
    // CVXIF transaction ID - ISSUE_STAGE
    output logic                   [CVA6Cfg.TRANS_ID_BITS-1:0] x_trans_id_o,
    // CVXIF exception - ISSUE_STAGE
    output exception_t                                         x_exception_o,
    // CVXIF FU result - ISSUE_STAGE
    output logic                   [         CVA6Cfg.XLEN-1:0] x_result_o,
    // CVXIF result valid - ISSUE_STAGE
    output logic                                               x_valid_o,
    // CVXIF write enable - ISSUE_STAGE
    output logic                                               x_we_o,
    // CVXIF request - SUBSYSTEM
    output cvxif_pkg::cvxif_req_t                              cvxif_req_o,
    // CVXIF response - SUBSYSTEM
    input  cvxif_pkg::cvxif_resp_t                             cvxif_resp_i
);
  localparam X_NUM_RS = ariane_pkg::NR_RGPR_PORTS;

  logic illegal_n, illegal_q;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] illegal_id_n, illegal_id_q;
  logic [31:0] illegal_instr_n, illegal_instr_q;
  logic [X_NUM_RS-1:0] rs_valid;

  if (cvxif_pkg::X_NUM_RS == 3) begin : gen_third_operand
    assign rs_valid = 3'b111;
  end else begin : gen_no_third_operand
    assign rs_valid = 2'b11;
  end

  always_comb begin
    cvxif_req_o = '0;
    cvxif_req_o.x_result_ready = 1'b1;
    x_ready_o = cvxif_resp_i.x_issue_ready;
    if (x_valid_i) begin
      cvxif_req_o.x_issue_valid     = x_valid_i;
      cvxif_req_o.x_issue_req.instr = x_off_instr_i;
      cvxif_req_o.x_issue_req.mode  = priv_lvl_i;
      cvxif_req_o.x_issue_req.id    = fu_data_i.trans_id;
      cvxif_req_o.x_issue_req.rs[0] = fu_data_i.operand_a;
      cvxif_req_o.x_issue_req.rs[1] = fu_data_i.operand_b;
      if (cvxif_pkg::X_NUM_RS == 3) begin
        cvxif_req_o.x_issue_req.rs[2] = fu_data_i.imm;
      end
      cvxif_req_o.x_issue_req.rs_valid   = rs_valid;
      cvxif_req_o.x_commit_valid         = x_valid_i;
      cvxif_req_o.x_commit.id            = fu_data_i.trans_id;
      cvxif_req_o.x_commit.x_commit_kill = 1'b0;
    end
  end

  always_comb begin
    illegal_n       = illegal_q;
    illegal_id_n    = illegal_id_q;
    illegal_instr_n = illegal_instr_q;
    if (~cvxif_resp_i.x_issue_resp.accept && cvxif_req_o.x_issue_valid && cvxif_resp_i.x_issue_ready && ~illegal_n) begin
      illegal_n       = 1'b1;
      illegal_id_n    = cvxif_req_o.x_issue_req.id;
      illegal_instr_n = cvxif_req_o.x_issue_req.instr;
    end
    x_valid_o = cvxif_resp_i.x_result_valid;  //Read result only when CVXIF is enabled
    x_trans_id_o = x_valid_o ? cvxif_resp_i.x_result.id : '0;
    x_result_o = x_valid_o ? cvxif_resp_i.x_result.data : '0;
    x_exception_o.cause   = x_valid_o ? {{(CVA6Cfg.XLEN-6){1'b0}}, cvxif_resp_i.x_result.exccode} : '0;
    x_exception_o.valid = x_valid_o ? cvxif_resp_i.x_result.exc : '0;
    x_exception_o.tval = '0;
    x_exception_o.tinst = '0;
    x_exception_o.tval2 = '0;
    x_exception_o.gva = '0;
    x_we_o = x_valid_o ? cvxif_resp_i.x_result.we : '0;
    if (illegal_n) begin
      if (~x_valid_o) begin
        x_trans_id_o = illegal_id_n;
        x_result_o = '0;
        x_valid_o = 1'b1;
        x_exception_o.cause = riscv::ILLEGAL_INSTR;
        x_exception_o.valid = 1'b1;
        if (CVA6Cfg.TvalEn) x_exception_o.tval = illegal_instr_n;
        x_exception_o.tinst = '0;
        x_exception_o.tval2 = '0;
        x_exception_o.gva = '0;
        x_we_o = '0;
        illegal_n             = '0; // Reset flag for illegal instr. illegal_id and illegal instr values are a don't care, no need to reset it.
      end
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      illegal_q       <= 1'b0;
      illegal_id_q    <= '0;
      illegal_instr_q <= '0;
    end else begin
      illegal_q       <= illegal_n;
      illegal_id_q    <= illegal_id_n;
      illegal_instr_q <= illegal_instr_n;
    end
  end

endmodule
