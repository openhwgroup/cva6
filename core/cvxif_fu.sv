// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Guillaume CHAUVON (guillaume.chauvon@thalesgroup.com)

// Functional Unit for the logic of the CoreV-X-Interface


module cvxif_fu import ariane_pkg::*; #(
    parameter ariane_pkg::cva6_cfg_t cva6_cfg = ariane_pkg::cva6_cfg_empty,
    parameter type x_req_t = core_v_xif_pkg::x_req_t,
    parameter type x_resp_t = core_v_xif_pkg::x_resp_t
) (
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
    output x_req_t                            core_v_xif_req_o,
    input  x_resp_t                           core_v_xif_resp_i
);

    logic illegal_n, illegal_q;
    logic [TRANS_ID_BITS-1:0] illegal_id_n, illegal_id_q;
    logic [31:0] illegal_instr_n, illegal_instr_q;

    always_comb begin
      core_v_xif_req_o = '0;
      core_v_xif_req_o.result_ready = 1'b1;
      x_ready_o = core_v_xif_resp_i.issue_ready;
      if (x_valid_i) begin
        core_v_xif_req_o.issue_valid          = x_valid_i;
        core_v_xif_req_o.issue_req.instr      = x_off_instr_i;
        core_v_xif_req_o.issue_req.id         = fu_data_i.trans_id;
        core_v_xif_req_o.issue_req.rs[0]      = fu_data_i.operand_a;
        core_v_xif_req_o.issue_req.rs[1]      = fu_data_i.operand_b;
        if (core_v_xif_pkg::X_NUM_RS == 3) begin
          core_v_xif_req_o.issue_req.rs[2]    = fu_data_i.imm;
        end
        core_v_xif_req_o.issue_req.rs_valid   = core_v_xif_pkg::X_NUM_RS == 3 ? 3'b111 : 2'b11;
        core_v_xif_req_o.commit_valid         = x_valid_i;
        core_v_xif_req_o.commit.id            = fu_data_i.trans_id;
        core_v_xif_req_o.commit.x_commit_kill = 1'b0;
      end
    end

    always_comb begin
      illegal_n       = illegal_q;
      illegal_id_n    = illegal_id_q;
      illegal_instr_n = illegal_instr_q;
      if (~core_v_xif_resp_i.issue_resp.accept && core_v_xif_req_o.issue_valid && core_v_xif_resp_i.issue_ready && ~illegal_n) begin
          illegal_n       = 1'b1;
          illegal_id_n    = core_v_xif_req_o.issue_req.id;
          illegal_instr_n = core_v_xif_req_o.issue_req.instr;
      end
      x_valid_o             = core_v_xif_resp_i.result_valid; //Read result only when CVXIF is enabled
      x_trans_id_o          = x_valid_o ? core_v_xif_resp_i.result.id : '0;
      x_result_o            = x_valid_o ? core_v_xif_resp_i.result.data : '0;
      x_exception_o.cause   = x_valid_o ? core_v_xif_resp_i.result.exccode : '0;
      x_exception_o.valid   = x_valid_o ? core_v_xif_resp_i.result.exc : '0;
      x_exception_o.tval    = '0;
      x_we_o                = x_valid_o ? core_v_xif_resp_i.result.we : '0;
      if (illegal_n) begin
        if (~x_valid_o) begin
          x_trans_id_o          = illegal_id_n;
          x_result_o            = '0;
          x_valid_o             = 1'b1;
          x_exception_o.cause   = riscv::ILLEGAL_INSTR;
          x_exception_o.valid   = 1'b1;
          x_exception_o.tval    = illegal_instr_n;
          x_we_o                = '0;
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
