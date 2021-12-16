// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Guillaume CHAUVON (guillaume.chauvon@thalesgroup.com)

// Functional Unit for the logic of the CoreV-X-Interface


module cvxif_fu import ariane_pkg::*; (
    input  logic                              clk_i,
    input  logic                              rst_ni,
    input  fu_data_t                          fu_data_i,
    //from issue
    input  logic                              x_valid_i,
    output logic                              x_ready_o,
    input  logic [31:0]                       x_off_instr_i,
    //to writeback
    output logic [TRANS_ID_BITS-1:0]          x_trans_id_o,
    output exception_t                        x_exception_o,
    output riscv::xlen_t                      x_result_o,
    output logic                              x_valid_o,
    output logic                              x_we_o,
    //to coprocessor
    output cvxif_pkg::cvxif_req_t             x_req_o,
    input  cvxif_pkg::cvxif_resp_t            x_resp_i
);

    always_comb begin
      x_req_o = '0;
      x_req_o.x_result_ready = 1;
      x_ready_o = x_resp_i.x_issue_ready;
      if (x_valid_i) begin
        x_req_o.x_issue_valid          = x_valid_i;
        x_req_o.x_issue_req.instr      = x_off_instr_i;
        x_req_o.x_issue_req.id         = fu_data_i.trans_id;
        x_req_o.x_issue_req.rs[0]      = fu_data_i.operand_a;
        x_req_o.x_issue_req.rs[1]      = fu_data_i.operand_b;
        if (cvxif_pkg::X_NUM_RS == 3)
          x_req_o.x_issue_req.rs[2]    = fu_data_i.imm;
        x_req_o.x_issue_req.rs_valid   = cvxif_pkg::X_NUM_RS == 3 ? 3'b111 : 2'b11;
        x_req_o.x_commit_valid         = x_valid_i;
        x_req_o.x_commit.id            = fu_data_i.trans_id;
        x_req_o.x_commit.x_commit_kill = 1'b0;
      end
    end

    always_comb begin
      if (~x_resp_i.x_issue_resp.accept && x_req_o.x_issue_valid && x_resp_i.x_issue_ready) begin
          x_trans_id_o          = x_req_o.x_issue_req.id;
          x_result_o            = 0;
          x_valid_o             = 1;
          x_exception_o.cause   = riscv::ILLEGAL_INSTR;
          x_exception_o.valid   = 1;
          x_exception_o.tval    = x_req_o.x_issue_req.instr;
          x_we_o                = '0;
      end
      else begin
          x_valid_o             = x_resp_i.x_result_valid;
          x_trans_id_o          = x_valid_o ? x_resp_i.x_result.id : '0;
          x_result_o            = x_valid_o ? x_resp_i.x_result.data : '0;
          x_exception_o.cause   = x_valid_o ? x_resp_i.x_result.exccode : '0;
          x_exception_o.valid   = x_valid_o ? x_resp_i.x_result.exc : '0;
          x_exception_o.tval    = '0;
          x_we_o                = x_valid_o ? x_resp_i.x_result.we : '0;
      end
    end

endmodule
