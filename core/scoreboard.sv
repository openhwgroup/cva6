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
// Date: 08.04.2017
// Description: Scoreboard - keeps track of all decoded, issued and committed instructions

module scoreboard #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type bp_resolve_t = logic,
    parameter type exception_t = logic,
    parameter type scoreboard_entry_t = logic,
    parameter type rs3_len_t = logic
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic sb_full_o,
    // Flush only un-issued instructions - TO_BE_COMPLETED
    input logic flush_unissued_instr_i,
    // Flush whole scoreboard - TO_BE_COMPLETED
    input logic flush_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output ariane_pkg::fu_t [2**ariane_pkg::REG_ADDR_SIZE-1:0] rd_clobber_gpr_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output ariane_pkg::fu_t [2**ariane_pkg::REG_ADDR_SIZE-1:0] rd_clobber_fpr_o,

    // rs1 operand address - issue_read_operands
    input  logic [ariane_pkg::SUPERSCALAR:0][ariane_pkg::REG_ADDR_SIZE-1:0] rs1_i,
    // rs1 operand - issue_read_operands
    output logic [ariane_pkg::SUPERSCALAR:0][             CVA6Cfg.XLEN-1:0] rs1_o,
    // rs1 operand is valid - issue_read_operands
    output logic [ariane_pkg::SUPERSCALAR:0]                                rs1_valid_o,

    // rs2 operand address - issue_read_operands
    input  logic [ariane_pkg::SUPERSCALAR:0][ariane_pkg::REG_ADDR_SIZE-1:0] rs2_i,
    // rs2 operand - issue_read_operands
    output logic [ariane_pkg::SUPERSCALAR:0][             CVA6Cfg.XLEN-1:0] rs2_o,
    // rs2 operand is valid - issue_read_operands
    output logic [ariane_pkg::SUPERSCALAR:0]                                rs2_valid_o,

    // rs3 operand address - issue_read_operands
    input  logic     [ariane_pkg::SUPERSCALAR:0][ariane_pkg::REG_ADDR_SIZE-1:0] rs3_i,
    // rs3 operand - issue_read_operands
    output rs3_len_t [ariane_pkg::SUPERSCALAR:0]                                rs3_o,
    // rs3 operand is valid - issue_read_operands
    output logic     [ariane_pkg::SUPERSCALAR:0]                                rs3_valid_o,

    // advertise instruction to commit stage, if commit_ack_i is asserted advance the commit pointer
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output scoreboard_entry_t [CVA6Cfg.NrCommitPorts-1:0] commit_instr_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic              [CVA6Cfg.NrCommitPorts-1:0] commit_drop_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic              [CVA6Cfg.NrCommitPorts-1:0] commit_ack_i,

    // instruction to put on top of scoreboard e.g.: top pointer
    // we can always put this instruction to the top unless we signal with asserted full_o
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  scoreboard_entry_t [ariane_pkg::SUPERSCALAR:0]       decoded_instr_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic              [ariane_pkg::SUPERSCALAR:0][31:0] orig_instr_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic              [ariane_pkg::SUPERSCALAR:0]       decoded_instr_valid_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic              [ariane_pkg::SUPERSCALAR:0]       decoded_instr_ack_o,

    // instruction to issue logic, if issue_instr_valid and issue_ready is asserted, advance the issue pointer
    // Issue scoreboard entry - ACC_DISPATCHER
    output scoreboard_entry_t [ariane_pkg::SUPERSCALAR:0]       issue_instr_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic              [ariane_pkg::SUPERSCALAR:0][31:0] orig_instr_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic              [ariane_pkg::SUPERSCALAR:0]       issue_instr_valid_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic              [ariane_pkg::SUPERSCALAR:0]       issue_ack_i,

    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input bp_resolve_t resolved_branch_i,
    // Transaction ID at which to write the result back - TO_BE_COMPLETED
    input logic [CVA6Cfg.NrWbPorts-1:0][CVA6Cfg.TRANS_ID_BITS-1:0] trans_id_i,
    // Results to write back - TO_BE_COMPLETED
    input logic [CVA6Cfg.NrWbPorts-1:0][CVA6Cfg.XLEN-1:0] wbdata_i,
    // Exception from a functional unit (e.g.: ld/st exception) - TO_BE_COMPLETED
    input exception_t [CVA6Cfg.NrWbPorts-1:0] ex_i,
    // Indicates valid results - TO_BE_COMPLETED
    input logic [CVA6Cfg.NrWbPorts-1:0] wt_valid_i,
    // Cvxif we for writeback - TO_BE_COMPLETED
    input logic x_we_i,

    // TO_BE_COMPLETED - RVFI
    output logic [ariane_pkg::SUPERSCALAR:0][CVA6Cfg.TRANS_ID_BITS-1:0] rvfi_issue_pointer_o,
    // TO_BE_COMPLETED - RVFI
    output logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.TRANS_ID_BITS-1:0] rvfi_commit_pointer_o
);

  // this is the FIFO struct of the issue queue
  typedef struct packed {
    logic issued;  // this bit indicates whether we issued this instruction e.g.: if it is valid
    logic cancelled;  // this instruction was cancelled (speculative scoreboard)
    logic is_rd_fpr_flag;  // redundant meta info, added for speed
    scoreboard_entry_t sbe;  // this is the score board entry we will send to ex
  } sb_mem_t;
  sb_mem_t [CVA6Cfg.NR_SB_ENTRIES-1:0] mem_q, mem_n;
  logic [CVA6Cfg.NR_SB_ENTRIES-1:0] still_issued;

  logic [ariane_pkg::SUPERSCALAR:0] issue_full;
  logic [1:0][CVA6Cfg.NR_SB_ENTRIES/2-1:0] issued_instrs_even_odd;

  logic bmiss;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] after_flu_wb;
  logic [CVA6Cfg.NR_SB_ENTRIES-1:0] speculative_instrs;

  logic [ariane_pkg::SUPERSCALAR:0] num_issue;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] issue_pointer_n, issue_pointer_q;
  logic [ariane_pkg::SUPERSCALAR+1:0][CVA6Cfg.TRANS_ID_BITS-1:0] issue_pointer;

  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.TRANS_ID_BITS-1:0] commit_pointer_n, commit_pointer_q;
  logic [$clog2(CVA6Cfg.NrCommitPorts):0] num_commit;

  for (genvar i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
    assign still_issued[i] = mem_q[i].issued & ~mem_q[i].cancelled;
  end

  for (genvar i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
    assign issued_instrs_even_odd[i%2][i/2] = mem_q[i].issued;
  end

  // the issue queue is full don't issue any new instructions
  assign issue_full[0] = &issued_instrs_even_odd[0] && &issued_instrs_even_odd[1];
  if (ariane_pkg::SUPERSCALAR) begin : assign_issue_full
    // Need two slots available to issue two instructions.
    // They are next to each other so one must be even and one odd
    assign issue_full[1] = &issued_instrs_even_odd[0] || &issued_instrs_even_odd[1];
  end

  assign sb_full_o = issue_full[0];

  // output commit instruction directly
  always_comb begin : commit_ports
    for (int unsigned i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      commit_instr_o[i] = mem_q[commit_pointer_q[i]].sbe;
      commit_instr_o[i].trans_id = commit_pointer_q[i];
      commit_drop_o[i] = mem_q[commit_pointer_q[i]].cancelled;
    end
  end

  assign issue_pointer[0] = issue_pointer_q;
  for (genvar i = 0; i <= ariane_pkg::SUPERSCALAR; i++) begin
    assign issue_pointer[i+1] = issue_pointer[i] + 'd1;
  end

  // an instruction is ready for issue if we have place in the issue FIFO and it the decoder says it is valid
  always_comb begin
    decoded_instr_ack_o = '0;
    issue_instr_o       = decoded_instr_i;
    orig_instr_o        = orig_instr_i;
    for (int unsigned i = 0; i <= ariane_pkg::SUPERSCALAR; i++) begin
      // make sure we assign the correct trans ID
      issue_instr_o[i].trans_id = issue_pointer[i];

      issue_instr_valid_o[i]    = decoded_instr_valid_i[i] & ~issue_full[i];
      decoded_instr_ack_o[i]    = issue_ack_i[i] & ~issue_full[i];
    end
  end

  // maintain a FIFO with issued instructions
  // keep track of all issued instructions
  always_comb begin : issue_fifo
    // default assignment
    mem_n     = mem_q;
    num_issue = '0;

    // if we got a acknowledge from the issue stage, put this scoreboard entry in the queue
    for (int unsigned i = 0; i <= ariane_pkg::SUPERSCALAR; i++) begin
      if (decoded_instr_valid_i[i] && decoded_instr_ack_o[i] && !flush_unissued_instr_i) begin
        // the decoded instruction we put in there is valid (1st bit)
        // increase the issue counter and advance issue pointer
        num_issue += 'd1;
        mem_n[issue_pointer[i]] = '{
            issued: 1'b1,
            cancelled: 1'b0,
            is_rd_fpr_flag: CVA6Cfg.FpPresent && ariane_pkg::is_rd_fpr(decoded_instr_i[i].op),
            sbe: decoded_instr_i[i]
        };
      end
    end

    // ------------
    // FU NONE
    // ------------
    for (int unsigned i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
      // The FU is NONE -> this instruction is valid immediately
      if (mem_q[i].sbe.fu == ariane_pkg::NONE && mem_q[i].issued) mem_n[i].sbe.valid = 1'b1;
    end

    // ------------
    // Write Back
    // ------------
    for (int unsigned i = 0; i < CVA6Cfg.NrWbPorts; i++) begin
      // check if this instruction was issued (e.g.: it could happen after a flush that there is still
      // something in the pipeline e.g. an incomplete memory operation)
      if (wt_valid_i[i] && mem_q[trans_id_i[i]].issued) begin
        if (mem_q[trans_id_i[i]].sbe.is_double_rd_macro_instr && mem_q[trans_id_i[i]].sbe.is_macro_instr) begin
          if (mem_q[trans_id_i[i]].sbe.is_last_macro_instr) begin
            mem_n[trans_id_i[i]].sbe.valid = 1'b1;
            mem_n[8'(trans_id_i[i])-1].sbe.valid = 1'b1;
          end else begin
            mem_n[trans_id_i[i]].sbe.valid = 1'b0;
          end
        end else begin
          mem_n[trans_id_i[i]].sbe.valid = 1'b1;
        end
        mem_n[trans_id_i[i]].sbe.result = wbdata_i[i];
        // save the target address of a branch (needed for debug in commit stage)
        if (CVA6Cfg.DebugEn) begin
          mem_n[trans_id_i[i]].sbe.bp.predict_address = resolved_branch_i.target_address;
        end
        if (mem_n[trans_id_i[i]].sbe.fu == ariane_pkg::CVXIF && ~x_we_i) begin
          mem_n[trans_id_i[i]].sbe.rd = 5'b0;
        end
        // write the exception back if it is valid
        if (ex_i[i].valid) mem_n[trans_id_i[i]].sbe.ex = ex_i[i];
        // write the fflags back from the FPU (exception valid is never set), leave tval intact
        else if(CVA6Cfg.FpPresent && (mem_q[trans_id_i[i]].sbe.fu == ariane_pkg::FPU || mem_q[trans_id_i[i]].sbe.fu == ariane_pkg::FPU_VEC)) begin
          mem_n[trans_id_i[i]].sbe.ex.cause = ex_i[i].cause;
        end
      end
    end

    // ------------
    // Cancel
    // ------------
    if (ariane_pkg::SPECULATIVE_SB) begin
      if (bmiss) begin
        for (int unsigned i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
          if (speculative_instrs[i]) begin
            mem_n[i].cancelled = 1'b1;
          end
        end
      end
    end

    // ------------
    // Commit Port
    // ------------
    // we've got an acknowledge from commit
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      if (commit_ack_i[i]) begin
        // this instruction is no longer in issue e.g.: it is considered finished
        mem_n[commit_pointer_q[i]].issued    = 1'b0;
        mem_n[commit_pointer_q[i]].cancelled = 1'b0;
        mem_n[commit_pointer_q[i]].sbe.valid = 1'b0;
      end
    end

    // ------
    // Flush
    // ------
    if (flush_i) begin
      for (int unsigned i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
        // set all valid flags for all entries to zero
        mem_n[i].issued       = 1'b0;
        mem_n[i].cancelled    = 1'b0;
        mem_n[i].sbe.valid    = 1'b0;
        mem_n[i].sbe.ex.valid = 1'b0;
      end
    end
  end

  assign bmiss = resolved_branch_i.valid && resolved_branch_i.is_mispredict;
  assign after_flu_wb = trans_id_i[ariane_pkg::FLU_WB] + 'd1;

  if (ariane_pkg::SPECULATIVE_SB) begin : find_speculative_instrs
    round_interval #(
        .S(CVA6Cfg.TRANS_ID_BITS)
    ) i_speculative_instrs (
        .start_i (after_flu_wb),
        .stop_i  (issue_pointer_q),
        .active_o(speculative_instrs)
    );
  end

  // FIFO counter updates
  if (CVA6Cfg.NrCommitPorts == 2) begin : gen_commit_ports
    assign num_commit = commit_ack_i[1] + commit_ack_i[0];
  end else begin : gen_one_commit_port
    assign num_commit = commit_ack_i[0];
  end

  assign commit_pointer_n[0] = (flush_i) ? '0 : commit_pointer_q[0] + num_commit;

  always_comb begin : assign_issue_pointer_n
    issue_pointer_n = issue_pointer[num_issue];
    if (flush_i) issue_pointer_n = '0;
  end

  // precompute offsets for commit slots
  for (genvar k = 1; k < CVA6Cfg.NrCommitPorts; k++) begin : gen_cnt_incr
    assign commit_pointer_n[k] = (flush_i) ? '0 : commit_pointer_n[0] + unsigned'(k);
  end

  // -------------------
  // RD clobber process
  // -------------------
  // rd_clobber output: output currently clobbered destination registers
  logic            [2**ariane_pkg::REG_ADDR_SIZE-1:0][CVA6Cfg.NR_SB_ENTRIES:0] gpr_clobber_vld;
  logic            [2**ariane_pkg::REG_ADDR_SIZE-1:0][CVA6Cfg.NR_SB_ENTRIES:0] fpr_clobber_vld;
  ariane_pkg::fu_t [         CVA6Cfg.NR_SB_ENTRIES:0]                          clobber_fu;

  always_comb begin : clobber_assign
    gpr_clobber_vld = '0;
    fpr_clobber_vld = '0;

    // default (highest entry hast lowest prio in arbiter tree below)
    clobber_fu[CVA6Cfg.NR_SB_ENTRIES] = ariane_pkg::NONE;
    for (int unsigned i = 0; i < 2 ** ariane_pkg::REG_ADDR_SIZE; i++) begin
      gpr_clobber_vld[i][CVA6Cfg.NR_SB_ENTRIES] = 1'b1;
      fpr_clobber_vld[i][CVA6Cfg.NR_SB_ENTRIES] = 1'b1;
    end

    // check for all valid entries and set the clobber accordingly
    for (int unsigned i = 0; i < CVA6Cfg.NR_SB_ENTRIES; i++) begin
      gpr_clobber_vld[mem_q[i].sbe.rd][i] = still_issued[i] & ~mem_q[i].is_rd_fpr_flag;
      fpr_clobber_vld[mem_q[i].sbe.rd][i] = still_issued[i] & mem_q[i].is_rd_fpr_flag;
      clobber_fu[i]                       = mem_q[i].sbe.fu;
    end

    // GPR[0] is always free
    gpr_clobber_vld[0] = '0;
  end

  for (genvar k = 0; k < 2 ** ariane_pkg::REG_ADDR_SIZE; k++) begin : gen_sel_clobbers
    // get fu that is going to clobber this register (there should be only one)
    rr_arb_tree #(
        .NumIn(CVA6Cfg.NR_SB_ENTRIES + 1),
        .DataType(ariane_pkg::fu_t),
        .ExtPrio(1'b1),
        .AxiVldRdy(1'b1)
    ) i_sel_gpr_clobbers (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .flush_i(1'b0),
        .rr_i   ('0),
        .req_i  (gpr_clobber_vld[k]),
        .gnt_o  (),
        .data_i (clobber_fu),
        .gnt_i  (1'b1),
        .req_o  (),
        .data_o (rd_clobber_gpr_o[k]),
        .idx_o  ()
    );
    if (CVA6Cfg.FpPresent) begin
      rr_arb_tree #(
          .NumIn(CVA6Cfg.NR_SB_ENTRIES + 1),
          .DataType(ariane_pkg::fu_t),
          .ExtPrio(1'b1),
          .AxiVldRdy(1'b1)
      ) i_sel_fpr_clobbers (
          .clk_i  (clk_i),
          .rst_ni (rst_ni),
          .flush_i(1'b0),
          .rr_i   ('0),
          .req_i  (fpr_clobber_vld[k]),
          .gnt_o  (),
          .data_i (clobber_fu),
          .gnt_i  (1'b1),
          .req_o  (),
          .data_o (rd_clobber_fpr_o[k]),
          .idx_o  ()
      );
    end
  end

  // ----------------------------------
  // Read Operands (a.k.a forwarding)
  // ----------------------------------
  // read operand interface: same logic as register file
  logic [ariane_pkg::SUPERSCALAR:0][CVA6Cfg.NR_SB_ENTRIES+CVA6Cfg.NrWbPorts-1:0]
      rs1_fwd_req, rs2_fwd_req, rs3_fwd_req;
  logic [ariane_pkg::SUPERSCALAR:0][CVA6Cfg.NR_SB_ENTRIES+CVA6Cfg.NrWbPorts-1:0][CVA6Cfg.XLEN-1:0] rs_data;
  logic [ariane_pkg::SUPERSCALAR:0] rs1_valid, rs2_valid, rs3_valid;

  // WB ports have higher prio than entries
  for (genvar i = 0; i <= ariane_pkg::SUPERSCALAR; i++) begin
    for (genvar k = 0; unsigned'(k) < CVA6Cfg.NrWbPorts; k++) begin : gen_rs_wb
      assign rs1_fwd_req[i][k] = (mem_q[trans_id_i[k]].sbe.rd == rs1_i[i]) & (~mem_q[trans_id_i[k]].cancelled) & wt_valid_i[k] & (~ex_i[k].valid) & (mem_q[trans_id_i[k]].is_rd_fpr_flag == (CVA6Cfg.FpPresent && ariane_pkg::is_rs1_fpr(
          issue_instr_o[i].op
      )));
      assign rs2_fwd_req[i][k] = (mem_q[trans_id_i[k]].sbe.rd == rs2_i[i]) & (~mem_q[trans_id_i[k]].cancelled) & wt_valid_i[k] & (~ex_i[k].valid) & (mem_q[trans_id_i[k]].is_rd_fpr_flag == (CVA6Cfg.FpPresent && ariane_pkg::is_rs2_fpr(
          issue_instr_o[i].op
      )));
      assign rs3_fwd_req[i][k] = (mem_q[trans_id_i[k]].sbe.rd == rs3_i[i]) & (~mem_q[trans_id_i[k]].cancelled) & wt_valid_i[k] & (~ex_i[k].valid) & (mem_q[trans_id_i[k]].is_rd_fpr_flag == (CVA6Cfg.FpPresent && ariane_pkg::is_imm_fpr(
          issue_instr_o[i].op
      )));
      assign rs_data[i][k] = wbdata_i[k];
    end
    for (genvar k = 0; unsigned'(k) < CVA6Cfg.NR_SB_ENTRIES; k++) begin : gen_rs_entries
      assign rs1_fwd_req[i][k+CVA6Cfg.NrWbPorts] = (mem_q[k].sbe.rd == rs1_i[i]) & still_issued[k] & mem_q[k].sbe.valid & (mem_q[k].is_rd_fpr_flag == (CVA6Cfg.FpPresent && ariane_pkg::is_rs1_fpr(
          issue_instr_o[i].op
      )));
      assign rs2_fwd_req[i][k+CVA6Cfg.NrWbPorts] = (mem_q[k].sbe.rd == rs2_i[i]) & still_issued[k] & mem_q[k].sbe.valid & (mem_q[k].is_rd_fpr_flag == (CVA6Cfg.FpPresent && ariane_pkg::is_rs2_fpr(
          issue_instr_o[i].op
      )));
      assign rs3_fwd_req[i][k+CVA6Cfg.NrWbPorts] = (mem_q[k].sbe.rd == rs3_i[i]) & still_issued[k] & mem_q[k].sbe.valid & (mem_q[k].is_rd_fpr_flag == (CVA6Cfg.FpPresent && ariane_pkg::is_imm_fpr(
          issue_instr_o[i].op
      )));
      assign rs_data[i][k+CVA6Cfg.NrWbPorts] = mem_q[k].sbe.result;
    end

    // check whether we are accessing GPR[0]
    assign rs1_valid_o[i] = rs1_valid[i] & ((|rs1_i[i]) | (CVA6Cfg.FpPresent && ariane_pkg::is_rs1_fpr(
        issue_instr_o[i].op
    )));
    assign rs2_valid_o[i] = rs2_valid[i] & ((|rs2_i[i]) | (CVA6Cfg.FpPresent && ariane_pkg::is_rs2_fpr(
        issue_instr_o[i].op
    )));
    assign rs3_valid_o[i] = CVA6Cfg.NrRgprPorts == 3 ? rs3_valid[i] & ((|rs3_i[i]) | (CVA6Cfg.FpPresent && ariane_pkg::is_imm_fpr(
        issue_instr_o[i].op
    ))) : rs3_valid[i];

    // use fixed prio here
    // this implicitly gives higher prio to WB ports
    rr_arb_tree #(
        .NumIn(CVA6Cfg.NR_SB_ENTRIES + CVA6Cfg.NrWbPorts),
        .DataWidth(CVA6Cfg.XLEN),
        .ExtPrio(1'b1),
        .AxiVldRdy(1'b1)
    ) i_sel_rs1 (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .flush_i(1'b0),
        .rr_i   ('0),
        .req_i  (rs1_fwd_req[i]),
        .gnt_o  (),
        .data_i (rs_data[i]),
        .gnt_i  (1'b1),
        .req_o  (rs1_valid[i]),
        .data_o (rs1_o[i]),
        .idx_o  ()
    );

    rr_arb_tree #(
        .NumIn(CVA6Cfg.NR_SB_ENTRIES + CVA6Cfg.NrWbPorts),
        .DataWidth(CVA6Cfg.XLEN),
        .ExtPrio(1'b1),
        .AxiVldRdy(1'b1)
    ) i_sel_rs2 (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .flush_i(1'b0),
        .rr_i   ('0),
        .req_i  (rs2_fwd_req[i]),
        .gnt_o  (),
        .data_i (rs_data[i]),
        .gnt_i  (1'b1),
        .req_o  (rs2_valid[i]),
        .data_o (rs2_o[i]),
        .idx_o  ()
    );

    logic [ariane_pkg::SUPERSCALAR:0][CVA6Cfg.XLEN-1:0] rs3;

    rr_arb_tree #(
        .NumIn(CVA6Cfg.NR_SB_ENTRIES + CVA6Cfg.NrWbPorts),
        .DataWidth(CVA6Cfg.XLEN),
        .ExtPrio(1'b1),
        .AxiVldRdy(1'b1)
    ) i_sel_rs3 (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .flush_i(1'b0),
        .rr_i   ('0),
        .req_i  (rs3_fwd_req[i]),
        .gnt_o  (),
        .data_i (rs_data[i]),
        .gnt_i  (1'b1),
        .req_o  (rs3_valid[i]),
        .data_o (rs3[i]),
        .idx_o  ()
    );

    if (CVA6Cfg.NrRgprPorts == 3) begin : gen_gp_three_port
      assign rs3_o[i] = rs3[i][riscv::XLEN-1:0];
    end else begin : gen_fp_three_port
      assign rs3_o[i] = rs3[i][CVA6Cfg.FLen-1:0];
    end
  end


  // sequential process
  always_ff @(posedge clk_i or negedge rst_ni) begin : regs
    if (!rst_ni) begin
      mem_q            <= '{default: sb_mem_t'(0)};
      commit_pointer_q <= '0;
      issue_pointer_q  <= '0;
    end else begin
      issue_pointer_q  <= issue_pointer_n;
      mem_q            <= mem_n;
      commit_pointer_q <= commit_pointer_n;
    end
  end

  //RVFI
  assign rvfi_issue_pointer_o  = issue_pointer[ariane_pkg::SUPERSCALAR:0];
  assign rvfi_commit_pointer_o = commit_pointer_q;

  //pragma translate_off
  initial begin
    assert (CVA6Cfg.NR_SB_ENTRIES == 2 ** CVA6Cfg.TRANS_ID_BITS)
    else $fatal(1, "Scoreboard size needs to be a power of two.");
  end

  // assert that zero is never set
  assert property (@(posedge clk_i) disable iff (!rst_ni) (rd_clobber_gpr_o[0] == ariane_pkg::NONE))
  else $fatal(1, "RD 0 should not bet set");
  // assert that we never acknowledge a commit if the instruction is not valid
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) commit_ack_i[0] |-> commit_instr_o[0].valid)
  else $fatal(1, "Commit acknowledged but instruction is not valid");
  if (CVA6Cfg.NrCommitPorts == 2) begin : gen_two_commit_ports
    assert property (
        @(posedge clk_i) disable iff (!rst_ni) commit_ack_i[1] |-> commit_instr_o[1].valid)
    else $fatal(1, "Commit acknowledged but instruction is not valid");
  end
  // assert that we never give an issue ack signal if the instruction is not valid
  for (genvar i = 0; i <= ariane_pkg::SUPERSCALAR; i++) begin
    assert property (
      @(posedge clk_i) disable iff (!rst_ni) issue_ack_i[i] |-> issue_instr_valid_o[i])
    else $fatal(1, "Issue acknowledged but instruction is not valid");
  end

  // there should never be more than one instruction writing the same destination register (except x0)
  // check that no functional unit is retiring with the same transaction id
  for (genvar i = 0; i < CVA6Cfg.NrWbPorts; i++) begin
    for (genvar j = 0; j < CVA6Cfg.NrWbPorts; j++) begin
      assert property (
        @(posedge clk_i) disable iff (!rst_ni) wt_valid_i[i] && wt_valid_i[j] && (i != j) |-> (trans_id_i[i] != trans_id_i[j]))
      else
        $fatal(
            1,
            "Two or more functional units are retiring instructions with the same transaction id!"
        );
    end
  end
  //pragma translate_on
endmodule
