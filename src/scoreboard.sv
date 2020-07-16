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
  parameter int unsigned NR_ENTRIES      = 8, // must be a power of 2
  parameter int unsigned NR_WB_PORTS     = 1,
  parameter int unsigned NR_COMMIT_PORTS = 2
) (
  input  logic                                                  clk_i,    // Clock
  input  logic                                                  rst_ni,   // Asynchronous reset active low
  output logic                                                  sb_full_o,
  input  logic                                                  flush_unissued_instr_i, // flush only un-issued instructions
  input  logic                                                  flush_i,  // flush whole scoreboard
  input  logic                                                  unresolved_branch_i, // we have an unresolved branch
  // list of clobbered registers to issue stage
  output ariane_pkg::fu_t [2**ariane_pkg::REG_ADDR_SIZE-1:0]    rd_clobber_gpr_o,
  output ariane_pkg::fu_t [2**ariane_pkg::REG_ADDR_SIZE-1:0]    rd_clobber_fpr_o,

  // regfile like interface to operand read stage
  input  logic [ariane_pkg::REG_ADDR_SIZE-1:0]                  rs1_i,
  output riscv::xlen_t                                          rs1_o,
  output logic                                                  rs1_valid_o,

  input  logic [ariane_pkg::REG_ADDR_SIZE-1:0]                  rs2_i,
  output riscv::xlen_t                                          rs2_o,
  output logic                                                  rs2_valid_o,

  input  logic [ariane_pkg::REG_ADDR_SIZE-1:0]                  rs3_i,
  output logic [ariane_pkg::FLEN-1:0]                           rs3_o,
  output logic                                                  rs3_valid_o,

  // advertise instruction to commit stage, if commit_ack_i is asserted advance the commit pointer
  output ariane_pkg::scoreboard_entry_t [NR_COMMIT_PORTS-1:0]   commit_instr_o,
  input  logic              [NR_COMMIT_PORTS-1:0]               commit_ack_i,

  // instruction to put on top of scoreboard e.g.: top pointer
  // we can always put this instruction to the top unless we signal with asserted full_o
  input  ariane_pkg::scoreboard_entry_t                         decoded_instr_i,
  input  logic                                                  decoded_instr_valid_i,
  output logic                                                  decoded_instr_ack_o,

  // instruction to issue logic, if issue_instr_valid and issue_ready is asserted, advance the issue pointer
  output ariane_pkg::scoreboard_entry_t                         issue_instr_o,
  output logic                                                  issue_instr_valid_o,
  input  logic                                                  issue_ack_i,

  // write-back port
  input ariane_pkg::bp_resolve_t                                resolved_branch_i,
  input logic [NR_WB_PORTS-1:0][ariane_pkg::TRANS_ID_BITS-1:0]  trans_id_i,  // transaction ID at which to write the result back
  input logic [NR_WB_PORTS-1:0][riscv::XLEN-1:0]                wbdata_i,    // write data in
  input ariane_pkg::exception_t [NR_WB_PORTS-1:0]               ex_i,        // exception from a functional unit (e.g.: ld/st exception)
  input logic [NR_WB_PORTS-1:0]                                 wt_valid_i   // data in is valid
);
  localparam int unsigned BITS_ENTRIES = $clog2(NR_ENTRIES);

  // this is the FIFO struct of the issue queue
  struct packed {
    logic                          issued;         // this bit indicates whether we issued this instruction e.g.: if it is valid
    logic                          is_rd_fpr_flag; // redundant meta info, added for speed
    ariane_pkg::scoreboard_entry_t sbe;            // this is the score board entry we will send to ex
  } mem_q [NR_ENTRIES-1:0], mem_n [NR_ENTRIES-1:0];

  logic                    issue_full, issue_en;
  logic [BITS_ENTRIES-1:0] issue_cnt_n,      issue_cnt_q;
  logic [BITS_ENTRIES-1:0] issue_pointer_n,  issue_pointer_q;
  logic [NR_COMMIT_PORTS-1:0][BITS_ENTRIES-1:0] commit_pointer_n, commit_pointer_q;
  logic [$clog2(NR_COMMIT_PORTS):0] num_commit;

  // the issue queue is full don't issue any new instructions
  // works since aligned to power of 2
  assign issue_full = &issue_cnt_q;

  assign sb_full_o = issue_full;

  // output commit instruction directly
  always_comb begin : commit_ports
    for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) begin
      commit_instr_o[i] = mem_q[commit_pointer_q[i]].sbe;
      commit_instr_o[i].trans_id = commit_pointer_q[i];
    end
  end

  // an instruction is ready for issue if we have place in the issue FIFO and it the decoder says it is valid
  always_comb begin
    issue_instr_o          = decoded_instr_i;
    // make sure we assign the correct trans ID
    issue_instr_o.trans_id = issue_pointer_q;
    // we are ready if we are not full and don't have any unresolved branches, but it can be
    // the case that we have an unresolved branch which is cleared in that cycle (resolved_branch_i == 1)
    issue_instr_valid_o    = decoded_instr_valid_i & ~unresolved_branch_i & ~issue_full;
    decoded_instr_ack_o    = issue_ack_i & ~issue_full;
  end

  // maintain a FIFO with issued instructions
  // keep track of all issued instructions
  always_comb begin : issue_fifo
    // default assignment
    mem_n          = mem_q;
    issue_en       = 1'b0;

    // if we got a acknowledge from the issue stage, put this scoreboard entry in the queue
    if (decoded_instr_valid_i && decoded_instr_ack_o && !flush_unissued_instr_i) begin
      // the decoded instruction we put in there is valid (1st bit)
      // increase the issue counter and advance issue pointer
      issue_en = 1'b1;
      mem_n[issue_pointer_q] = {1'b1,                                      // valid bit
                                ariane_pkg::is_rd_fpr(decoded_instr_i.op), // whether rd goes to the fpr
                                decoded_instr_i                            // decoded instruction record
                                };
    end

    // ------------
    // FU NONE
    // ------------
    for (int unsigned i = 0; i < NR_ENTRIES; i++) begin
      // The FU is NONE -> this instruction is valid immediately
      if (mem_q[i].sbe.fu == ariane_pkg::NONE && mem_q[i].issued)
        mem_n[i].sbe.valid = 1'b1;
    end

    // ------------
    // Write Back
    // ------------
    for (int unsigned i = 0; i < NR_WB_PORTS; i++) begin
      // check if this instruction was issued (e.g.: it could happen after a flush that there is still
      // something in the pipeline e.g. an incomplete memory operation)
      if (wt_valid_i[i] && mem_q[trans_id_i[i]].issued) begin
        mem_n[trans_id_i[i]].sbe.valid  = 1'b1;
        mem_n[trans_id_i[i]].sbe.result = wbdata_i[i];
        // save the target address of a branch (needed for debug in commit stage)
        mem_n[trans_id_i[i]].sbe.bp.predict_address = resolved_branch_i.target_address;
        // write the exception back if it is valid
        if (ex_i[i].valid)
          mem_n[trans_id_i[i]].sbe.ex = ex_i[i];
        // write the fflags back from the FPU (exception valid is never set), leave tval intact
        else if (mem_q[trans_id_i[i]].sbe.fu inside {ariane_pkg::FPU, ariane_pkg::FPU_VEC})
          mem_n[trans_id_i[i]].sbe.ex.cause = ex_i[i].cause;
      end
    end

    // ------------
    // Commit Port
    // ------------
    // we've got an acknowledge from commit
    for (logic [BITS_ENTRIES-1:0] i = 0; i < NR_COMMIT_PORTS; i++) begin
      if (commit_ack_i[i]) begin
        // this instruction is no longer in issue e.g.: it is considered finished
        mem_n[commit_pointer_q[i]].issued     = 1'b0;
        mem_n[commit_pointer_q[i]].sbe.valid  = 1'b0;
      end
    end

    // ------
    // Flush
    // ------
    if (flush_i) begin
      for (int unsigned i = 0; i < NR_ENTRIES; i++) begin
        // set all valid flags for all entries to zero
        mem_n[i].issued       = 1'b0;
        mem_n[i].sbe.valid    = 1'b0;
        mem_n[i].sbe.ex.valid = 1'b0;
      end
    end
  end

  // FIFO counter updates
  popcount #(
    .INPUT_WIDTH(NR_COMMIT_PORTS)
  ) i_popcount (
    .data_i(commit_ack_i),
    .popcount_o(num_commit)
  );

  assign issue_cnt_n         = (flush_i) ? '0 : issue_cnt_q         - num_commit + issue_en;
  assign commit_pointer_n[0] = (flush_i) ? '0 : commit_pointer_q[0] + num_commit;
  assign issue_pointer_n     = (flush_i) ? '0 : issue_pointer_q     + issue_en;

  // precompute offsets for commit slots
  for (genvar k=1; k < NR_COMMIT_PORTS; k++) begin : gen_cnt_incr
    assign commit_pointer_n[k] = (flush_i) ? '0 : commit_pointer_n[0] + unsigned'(k);
  end

  // -------------------
  // RD clobber process
  // -------------------
  // rd_clobber output: output currently clobbered destination registers
  logic [2**ariane_pkg::REG_ADDR_SIZE-1:0][NR_ENTRIES:0]              gpr_clobber_vld;
  logic [2**ariane_pkg::REG_ADDR_SIZE-1:0][NR_ENTRIES:0]              fpr_clobber_vld;
  ariane_pkg::fu_t [NR_ENTRIES:0]                                     clobber_fu;

  always_comb begin : clobber_assign
    gpr_clobber_vld  = '0;
    fpr_clobber_vld  = '0;

    // default (highest entry hast lowest prio in arbiter tree below)
    clobber_fu[NR_ENTRIES] = ariane_pkg::NONE;
    for (int unsigned i = 0; i < 2**ariane_pkg::REG_ADDR_SIZE; i++) begin
      gpr_clobber_vld[i][NR_ENTRIES] = 1'b1;
      fpr_clobber_vld[i][NR_ENTRIES] = 1'b1;
    end

    // check for all valid entries and set the clobber accordingly
    for (int unsigned i = 0; i < NR_ENTRIES; i++) begin
      gpr_clobber_vld[mem_q[i].sbe.rd][i] = mem_q[i].issued & ~mem_q[i].is_rd_fpr_flag;
      fpr_clobber_vld[mem_q[i].sbe.rd][i] = mem_q[i].issued & mem_q[i].is_rd_fpr_flag;
      clobber_fu[i]                       = mem_q[i].sbe.fu;
    end

    // GPR[0] is always free
    gpr_clobber_vld[0] = '0;
  end

  for (genvar k = 0; k < 2**ariane_pkg::REG_ADDR_SIZE; k++) begin : gen_sel_clobbers
    // get fu that is going to clobber this register (there should be only one)
    rr_arb_tree #(
      .NumIn(NR_ENTRIES+1),
      .DataType(ariane_pkg::fu_t),
      .ExtPrio(1'b1),
      .AxiVldRdy(1'b1)
    ) i_sel_gpr_clobbers (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .flush_i ( 1'b0                ),
      .rr_i    ( '0                  ),
      .req_i   ( gpr_clobber_vld[k]  ),
      .gnt_o   (                     ),
      .data_i  ( clobber_fu          ),
      .gnt_i   ( 1'b1                ),
      .req_o   (                     ),
      .data_o  ( rd_clobber_gpr_o[k] ),
      .idx_o   (                     )
    );
    rr_arb_tree #(
      .NumIn(NR_ENTRIES+1),
      .DataType(ariane_pkg::fu_t),
      .ExtPrio(1'b1),
      .AxiVldRdy(1'b1)
    ) i_sel_fpr_clobbers (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .flush_i ( 1'b0                ),
      .rr_i    ( '0                  ),
      .req_i   ( fpr_clobber_vld[k]  ),
      .gnt_o   (                     ),
      .data_i  ( clobber_fu          ),
      .gnt_i   ( 1'b1                ),
      .req_o   (                     ),
      .data_o  ( rd_clobber_fpr_o[k] ),
      .idx_o   (                     )
    );
  end

  // ----------------------------------
  // Read Operands (a.k.a forwarding)
  // ----------------------------------
  // read operand interface: same logic as register file
  logic [NR_ENTRIES+NR_WB_PORTS-1:0] rs1_fwd_req, rs2_fwd_req, rs3_fwd_req;
  logic [NR_ENTRIES+NR_WB_PORTS-1:0][riscv::XLEN-1:0] rs_data;
  logic rs1_valid, rs2_valid;

  // WB ports have higher prio than entries
  for (genvar k = 0; unsigned'(k) < NR_WB_PORTS; k++) begin : gen_rs_wb
    assign rs1_fwd_req[k] = (mem_q[trans_id_i[k]].sbe.rd == rs1_i) & wt_valid_i[k] & (~ex_i[k].valid) & (mem_q[trans_id_i[k]].is_rd_fpr_flag == ariane_pkg::is_rs1_fpr(issue_instr_o.op));
    assign rs2_fwd_req[k] = (mem_q[trans_id_i[k]].sbe.rd == rs2_i) & wt_valid_i[k] & (~ex_i[k].valid) & (mem_q[trans_id_i[k]].is_rd_fpr_flag == ariane_pkg::is_rs2_fpr(issue_instr_o.op));
    assign rs3_fwd_req[k] = (mem_q[trans_id_i[k]].sbe.rd == rs3_i) & wt_valid_i[k] & (~ex_i[k].valid) & (mem_q[trans_id_i[k]].is_rd_fpr_flag == ariane_pkg::is_imm_fpr(issue_instr_o.op));
    assign rs_data[k]     = wbdata_i[k];
  end
  for (genvar k = 0; unsigned'(k) < NR_ENTRIES; k++) begin : gen_rs_entries
    assign rs1_fwd_req[k+NR_WB_PORTS] = (mem_q[k].sbe.rd == rs1_i) & mem_q[k].issued & mem_q[k].sbe.valid & (mem_q[k].is_rd_fpr_flag == ariane_pkg::is_rs1_fpr(issue_instr_o.op));
    assign rs2_fwd_req[k+NR_WB_PORTS] = (mem_q[k].sbe.rd == rs2_i) & mem_q[k].issued & mem_q[k].sbe.valid & (mem_q[k].is_rd_fpr_flag == ariane_pkg::is_rs2_fpr(issue_instr_o.op));
    assign rs3_fwd_req[k+NR_WB_PORTS] = (mem_q[k].sbe.rd == rs3_i) & mem_q[k].issued & mem_q[k].sbe.valid & (mem_q[k].is_rd_fpr_flag == ariane_pkg::is_imm_fpr(issue_instr_o.op));
    assign rs_data[k+NR_WB_PORTS]     = mem_q[k].sbe.result;
  end

  // check whether we are accessing GPR[0], rs3 is only used with the FPR!
  assign rs1_valid_o = rs1_valid & ((|rs1_i) | ariane_pkg::is_rs1_fpr(issue_instr_o.op));
  assign rs2_valid_o = rs2_valid & ((|rs2_i) | ariane_pkg::is_rs2_fpr(issue_instr_o.op));

  // use fixed prio here
  // this implicitly gives higher prio to WB ports
  rr_arb_tree #(
    .NumIn(NR_ENTRIES+NR_WB_PORTS),
    .DataWidth(riscv::XLEN),
    .ExtPrio(1'b1),
    .AxiVldRdy(1'b1)
  ) i_sel_rs1 (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .flush_i ( 1'b0        ),
    .rr_i    ( '0          ),
    .req_i   ( rs1_fwd_req ),
    .gnt_o   (             ),
    .data_i  ( rs_data     ),
    .gnt_i   ( 1'b1        ),
    .req_o   ( rs1_valid   ),
    .data_o  ( rs1_o       ),
    .idx_o   (             )
  );

  rr_arb_tree #(
    .NumIn(NR_ENTRIES+NR_WB_PORTS),
    .DataWidth(riscv::XLEN),
    .ExtPrio(1'b1),
    .AxiVldRdy(1'b1)
  ) i_sel_rs2 (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .flush_i ( 1'b0        ),
    .rr_i    ( '0          ),
    .req_i   ( rs2_fwd_req ),
    .gnt_o   (             ),
    .data_i  ( rs_data     ),
    .gnt_i   ( 1'b1        ),
    .req_o   ( rs2_valid   ),
    .data_o  ( rs2_o       ),
    .idx_o   (             )
  );

  riscv::xlen_t           rs3;

  rr_arb_tree #(
    .NumIn(NR_ENTRIES+NR_WB_PORTS),
    .DataWidth(riscv::XLEN),
    .ExtPrio(1'b1),
    .AxiVldRdy(1'b1)
  ) i_sel_rs3 (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .flush_i ( 1'b0        ),
    .rr_i    ( '0          ),
    .req_i   ( rs3_fwd_req ),
    .gnt_o   (             ),
    .data_i  ( rs_data     ),
    .gnt_i   ( 1'b1        ),
    .req_o   ( rs3_valid_o ),
    .data_o  ( rs3         ),
    .idx_o   (             )
  );

  assign rs3_o = rs3[ariane_pkg::FLEN-1:0];

  // sequential process
  always_ff @(posedge clk_i or negedge rst_ni) begin : regs
    if(!rst_ni) begin
      mem_q                 <= '{default: 0};
      issue_cnt_q           <= '0;
      commit_pointer_q      <= '0;
      issue_pointer_q       <= '0;
    end else begin
      issue_cnt_q           <= issue_cnt_n;
      issue_pointer_q       <= issue_pointer_n;
      mem_q                 <= mem_n;
      commit_pointer_q      <= commit_pointer_n;
    end
  end

  //pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (NR_ENTRIES == 2**BITS_ENTRIES) else $fatal("Scoreboard size needs to be a power of two.");
  end

  // assert that zero is never set
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) (rd_clobber_gpr_o[0] == ariane_pkg::NONE))
    else $fatal (1,"RD 0 should not bet set");
  // assert that we never acknowledge a commit if the instruction is not valid
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) commit_ack_i[0] |-> commit_instr_o[0].valid)
    else $fatal (1,"Commit acknowledged but instruction is not valid");

  assert property (
    @(posedge clk_i) disable iff (!rst_ni) commit_ack_i[1] |-> commit_instr_o[1].valid)
    else $fatal (1,"Commit acknowledged but instruction is not valid");

  // assert that we never give an issue ack signal if the instruction is not valid
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) issue_ack_i |-> issue_instr_valid_o)
    else $fatal (1,"Issue acknowledged but instruction is not valid");

  // there should never be more than one instruction writing the same destination register (except x0)
  // check that no functional unit is retiring with the same transaction id
  for (genvar i = 0; i < NR_WB_PORTS; i++) begin
    for (genvar j = 0; j < NR_WB_PORTS; j++)  begin
      assert property (
        @(posedge clk_i) disable iff (!rst_ni) wt_valid_i[i] && wt_valid_i[j] && (i != j) |-> (trans_id_i[i] != trans_id_i[j]))
        else $fatal (1,"Two or more functional units are retiring instructions with the same transaction id!");
    end
  end
  `endif
  //pragma translate_on
endmodule
