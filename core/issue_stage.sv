// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 21.05.2017
// Description: Issue stage dispatches instructions to the FUs and keeps track of them
//              in a scoreboard like data-structure.


module issue_stage
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type bp_resolve_t = logic,
    parameter type branchpredict_sbe_t = logic,
    parameter type exception_t = logic,
    parameter type fu_data_t = logic,
    parameter type scoreboard_entry_t = logic
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // Is scoreboard full - PERF_COUNTERS
    output logic sb_full_o,
    // TO_BE_COMPLETED - CONTROLLER
    input logic flush_unissued_instr_i,
    // TO_BE_COMPLETED - CONTROLLER
    input logic flush_i,
    // Stall inserted by Acc dispatcher - ACC_DISPATCHER
    input logic stall_i,
    // Handshake's data with decode stage - ID_STAGE
    input scoreboard_entry_t [SUPERSCALAR:0] decoded_instr_i,
    // instruction value - ID_STAGE
    input logic [SUPERSCALAR:0][31:0] orig_instr_i,
    // Handshake's valid with decode stage - ID_STAGE
    input logic [SUPERSCALAR:0] decoded_instr_valid_i,
    // Is instruction a control flow instruction - ID_STAGE
    input logic [SUPERSCALAR:0] is_ctrl_flow_i,
    // Handshake's acknowlege with decode stage - ID_STAGE
    output logic [SUPERSCALAR:0] decoded_instr_ack_o,
    // rs1 forwarding - EX_STAGE
    output [SUPERSCALAR:0][CVA6Cfg.VLEN-1:0] rs1_forwarding_o,
    // rs2 forwarding - EX_STAGE
    output [SUPERSCALAR:0][CVA6Cfg.VLEN-1:0] rs2_forwarding_o,
    // FU data useful to execute instruction - EX_STAGE
    output fu_data_t [SUPERSCALAR:0] fu_data_o,
    // Program Counter - EX_STAGE
    output logic [CVA6Cfg.VLEN-1:0] pc_o,
    // Is compressed instruction - EX_STAGE
    output logic is_compressed_instr_o,
    // Transformed trap instruction - EX_STAGE
    output logic [SUPERSCALAR:0][31:0] tinst_o,
    // Fixed Latency Unit is ready - EX_STAGE
    input logic flu_ready_i,
    // ALU FU is valid - EX_STAGE
    output logic [SUPERSCALAR:0] alu_valid_o,
    // Signaling that we resolved the branch - EX_STAGE
    input logic resolve_branch_i,
    // Load store unit FU is ready - EX_STAGE
    input logic lsu_ready_i,
    // Load store unit FU is valid - EX_STAGE
    output logic [SUPERSCALAR:0] lsu_valid_o,
    // Branch unit is valid - EX_STAGE
    output logic [SUPERSCALAR:0] branch_valid_o,
    // Information of branch prediction - EX_STAGE
    output branchpredict_sbe_t branch_predict_o,
    // Mult FU is valid - EX_STAGE
    output logic [SUPERSCALAR:0] mult_valid_o,
    // FPU FU is ready - EX_STAGE
    input logic fpu_ready_i,
    // FPU FU is valid - EX_STAGE
    output logic [SUPERSCALAR:0] fpu_valid_o,
    // FPU fmt field - EX_STAGE
    output logic [1:0] fpu_fmt_o,
    // FPU rm field - EX_STAGE
    output logic [2:0] fpu_rm_o,
    // ALU2 FU is valid - EX_STAGE
    output logic [SUPERSCALAR:0] alu2_valid_o,
    // CSR is valid - EX_STAGE
    output logic [SUPERSCALAR:0] csr_valid_o,
    // CVXIF FU is valid - EX_STAGE
    output logic [SUPERSCALAR:0] x_issue_valid_o,
    // CVXIF is FU ready - EX_STAGE
    input logic x_issue_ready_i,
    // CVXIF offloader instruction value - EX_STAGE
    output logic [31:0] x_off_instr_o,
    // Issue scoreboard entry - ACC_DISPATCHER
    output scoreboard_entry_t issue_instr_o,
    // TO_BE_COMPLETED - ACC_DISPATCHER
    output logic issue_instr_hs_o,
    // Transaction ID - EX_STAGE
    input logic [CVA6Cfg.NrWbPorts-1:0][CVA6Cfg.TRANS_ID_BITS-1:0] trans_id_i,
    // The branch engine uses the write back from the ALU - EX_STAGE
    input bp_resolve_t resolved_branch_i,
    // TO_BE_COMPLETED - EX_STAGE
    input logic [CVA6Cfg.NrWbPorts-1:0][CVA6Cfg.XLEN-1:0] wbdata_i,
    // exception from execute stage or CVXIF - EX_STAGE
    input exception_t [CVA6Cfg.NrWbPorts-1:0] ex_ex_i,
    // TO_BE_COMPLETED - EX_STAGE
    input logic [CVA6Cfg.NrWbPorts-1:0] wt_valid_i,
    // CVXIF write enable - EX_STAGE
    input logic x_we_i,
    // TO_BE_COMPLETED - EX_STAGE
    input logic [CVA6Cfg.NrCommitPorts-1:0][4:0] waddr_i,
    // TO_BE_COMPLETED - EX_STAGE
    input logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] wdata_i,
    // GPR write enable - EX_STAGE
    input logic [CVA6Cfg.NrCommitPorts-1:0] we_gpr_i,
    // FPR write enable - EX_STAGE
    input logic [CVA6Cfg.NrCommitPorts-1:0] we_fpr_i,
    // Instructions to commit - COMMIT_STAGE
    output scoreboard_entry_t [CVA6Cfg.NrCommitPorts-1:0] commit_instr_o,
    // Instruction is cancelled - COMMIT_STAGE
    output logic [CVA6Cfg.NrCommitPorts-1:0] commit_drop_o,
    // Commit acknowledge - COMMIT_STAGE
    input logic [CVA6Cfg.NrCommitPorts-1:0] commit_ack_i,
    // Issue stall - PERF_COUNTERS
    output logic stall_issue_o,
    // Information dedicated to RVFI - RVFI
    output logic [SUPERSCALAR:0][CVA6Cfg.TRANS_ID_BITS-1:0] rvfi_issue_pointer_o,
    // Information dedicated to RVFI - RVFI
    output logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.TRANS_ID_BITS-1:0] rvfi_commit_pointer_o
);
  // ---------------------------------------------------
  // Scoreboard (SB) <-> Issue and Read Operands (IRO)
  // ---------------------------------------------------
  typedef logic [(CVA6Cfg.NrRgprPorts == 3 ? CVA6Cfg.XLEN : CVA6Cfg.FLen)-1:0] rs3_len_t;

  fu_t               [2**REG_ADDR_SIZE-1:0]                    rd_clobber_gpr_sb_iro;
  fu_t               [2**REG_ADDR_SIZE-1:0]                    rd_clobber_fpr_sb_iro;

  logic              [       SUPERSCALAR:0][REG_ADDR_SIZE-1:0] rs1_iro_sb;
  logic              [       SUPERSCALAR:0][ CVA6Cfg.XLEN-1:0] rs1_sb_iro;
  logic              [       SUPERSCALAR:0]                    rs1_valid_sb_iro;

  logic              [       SUPERSCALAR:0][REG_ADDR_SIZE-1:0] rs2_iro_sb;
  logic              [       SUPERSCALAR:0][ CVA6Cfg.XLEN-1:0] rs2_sb_iro;
  logic              [       SUPERSCALAR:0]                    rs2_valid_iro_sb;

  logic              [       SUPERSCALAR:0][REG_ADDR_SIZE-1:0] rs3_iro_sb;
  rs3_len_t          [       SUPERSCALAR:0]                    rs3_sb_iro;
  logic              [       SUPERSCALAR:0]                    rs3_valid_iro_sb;

  scoreboard_entry_t [       SUPERSCALAR:0]                    issue_instr_sb_iro;
  logic              [       SUPERSCALAR:0][             31:0] orig_instr_sb_iro;
  logic              [       SUPERSCALAR:0]                    issue_instr_valid_sb_iro;
  logic              [       SUPERSCALAR:0]                    issue_ack_iro_sb;

  logic              [       SUPERSCALAR:0][ CVA6Cfg.XLEN-1:0] rs1_forwarding_xlen;
  logic              [       SUPERSCALAR:0][ CVA6Cfg.XLEN-1:0] rs2_forwarding_xlen;

  for (genvar i = 0; i <= SUPERSCALAR; i++) begin
    assign rs1_forwarding_o[i] = rs1_forwarding_xlen[i][CVA6Cfg.VLEN-1:0];
    assign rs2_forwarding_o[i] = rs2_forwarding_xlen[i][CVA6Cfg.VLEN-1:0];
  end

  assign issue_instr_o    = issue_instr_sb_iro[0];
  assign issue_instr_hs_o = issue_instr_valid_sb_iro[0] & issue_ack_iro_sb[0];


  // ---------------------------------------------------------
  // 2. Manage instructions in a scoreboard
  // ---------------------------------------------------------
  scoreboard #(
      .CVA6Cfg   (CVA6Cfg),
      .rs3_len_t (rs3_len_t),
      .bp_resolve_t(bp_resolve_t),
      .exception_t(exception_t),
      .scoreboard_entry_t(scoreboard_entry_t)
  ) i_scoreboard (
      .sb_full_o       (sb_full_o),
      .rd_clobber_gpr_o(rd_clobber_gpr_sb_iro),
      .rd_clobber_fpr_o(rd_clobber_fpr_sb_iro),
      .rs1_i           (rs1_iro_sb),
      .rs1_o           (rs1_sb_iro),
      .rs1_valid_o     (rs1_valid_sb_iro),
      .rs2_i           (rs2_iro_sb),
      .rs2_o           (rs2_sb_iro),
      .rs2_valid_o     (rs2_valid_iro_sb),
      .rs3_i           (rs3_iro_sb),
      .rs3_o           (rs3_sb_iro),
      .rs3_valid_o     (rs3_valid_iro_sb),

      .decoded_instr_i      (decoded_instr_i),
      .decoded_instr_valid_i(decoded_instr_valid_i),
      .decoded_instr_ack_o  (decoded_instr_ack_o),
      .issue_instr_o        (issue_instr_sb_iro),
      .orig_instr_o         (orig_instr_sb_iro),
      .issue_instr_valid_o  (issue_instr_valid_sb_iro),
      .issue_ack_i          (issue_ack_iro_sb),

      .resolved_branch_i(resolved_branch_i),
      .trans_id_i       (trans_id_i),
      .wbdata_i         (wbdata_i),
      .ex_i             (ex_ex_i),
      .*
  );

  // ---------------------------------------------------------
  // 3. Issue instruction and read operand, also commit
  // ---------------------------------------------------------
  issue_read_operands #(
      .CVA6Cfg(CVA6Cfg),
      .branchpredict_sbe_t(branchpredict_sbe_t),
      .fu_data_t(fu_data_t),
      .scoreboard_entry_t(scoreboard_entry_t),
      .rs3_len_t(rs3_len_t)
  ) i_issue_read_operands (
      .flush_i            (flush_unissued_instr_i),
      .issue_instr_i      (issue_instr_sb_iro),
      .orig_instr_i       (orig_instr_sb_iro),
      .issue_instr_valid_i(issue_instr_valid_sb_iro),
      .issue_ack_o        (issue_ack_iro_sb),
      .fu_data_o          (fu_data_o),
      .flu_ready_i        (flu_ready_i),
      .rs1_o              (rs1_iro_sb),
      .rs1_i              (rs1_sb_iro),
      .rs1_valid_i        (rs1_valid_sb_iro),
      .rs2_o              (rs2_iro_sb),
      .rs2_i              (rs2_sb_iro),
      .rs2_valid_i        (rs2_valid_iro_sb),
      .rs3_o              (rs3_iro_sb),
      .rs3_i              (rs3_sb_iro),
      .rs3_valid_i        (rs3_valid_iro_sb),
      .rd_clobber_gpr_i   (rd_clobber_gpr_sb_iro),
      .rd_clobber_fpr_i   (rd_clobber_fpr_sb_iro),
      .alu_valid_o        (alu_valid_o),
      .alu2_valid_o       (alu2_valid_o),
      .branch_valid_o     (branch_valid_o),
      .csr_valid_o        (csr_valid_o),
      .cvxif_valid_o      (x_issue_valid_o),
      .cvxif_ready_i      (x_issue_ready_i),
      .cvxif_off_instr_o  (x_off_instr_o),
      .mult_valid_o       (mult_valid_o),
      .rs1_forwarding_o   (rs1_forwarding_xlen),
      .rs2_forwarding_o   (rs2_forwarding_xlen),
      .stall_issue_o      (stall_issue_o),
      .tinst_o            (tinst_o),
      .*
  );

endmodule
