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


module issue_stage import ariane_pkg::*; #(
    parameter int unsigned NR_ENTRIES = 8,
    parameter int unsigned NR_WB_PORTS = 4,
    parameter int unsigned NR_COMMIT_PORTS = 2
)(
    input  logic                                     clk_i,     // Clock
    input  logic                                     rst_ni,    // Asynchronous reset active low

    output logic                                     sb_full_o,
    input  logic                                     flush_unissued_instr_i,
    input  logic                                     flush_i,
    // from ISSUE
    input  scoreboard_entry_t                        decoded_instr_i,
    input  logic                                     decoded_instr_valid_i,
    input  logic                                     is_ctrl_flow_i,
    output logic                                     decoded_instr_ack_o,
    // to EX
    output [riscv::VLEN-1:0]                         rs1_forwarding_o,  // unregistered version of fu_data_o.operanda
    output [riscv::VLEN-1:0]                         rs2_forwarding_o, // unregistered version of fu_data_o.operandb
    output fu_data_t                                 fu_data_o,
    output logic [riscv::VLEN-1:0]                   pc_o,
    output logic                                     is_compressed_instr_o,
    input  logic                                     flu_ready_i,
    output logic                                     alu_valid_o,
    // ex just resolved our predicted branch, we are ready to accept new requests
    input  logic                                     resolve_branch_i,

    input  logic                                     lsu_ready_i,
    output logic                                     lsu_valid_o,
    // branch prediction
    output logic                                     branch_valid_o,   // use branch prediction unit
    output branchpredict_sbe_t                       branch_predict_o, // Branch predict Out

    output logic                                     mult_valid_o,

    input  logic                                     fpu_ready_i,
    output logic                                     fpu_valid_o,
    output logic [1:0]                               fpu_fmt_o,        // FP fmt field from instr.
    output logic [2:0]                               fpu_rm_o,         // FP rm field from instr.

    output logic                                     csr_valid_o,

    // CVXIF
    //Issue interface
    output logic                                     x_issue_valid_o,
    input  logic                                     x_issue_ready_i,
    output logic [31:0]                              x_off_instr_o,

    // write back port
    input logic [NR_WB_PORTS-1:0][TRANS_ID_BITS-1:0] trans_id_i,
    input bp_resolve_t                               resolved_branch_i,
    input logic [NR_WB_PORTS-1:0][riscv::XLEN-1:0]   wbdata_i,
    input exception_t [NR_WB_PORTS-1:0]              ex_ex_i, // exception from execute stage or CVXIF offloaded instruction
    input logic [NR_WB_PORTS-1:0]                    wt_valid_i,
    input logic                                      x_we_i,

    // commit port
    input  logic [NR_COMMIT_PORTS-1:0][4:0]          waddr_i,
    input  logic [NR_COMMIT_PORTS-1:0][riscv::XLEN-1:0] wdata_i,
    input  logic [NR_COMMIT_PORTS-1:0]               we_gpr_i,
    input  logic [NR_COMMIT_PORTS-1:0]               we_fpr_i,

    output scoreboard_entry_t [NR_COMMIT_PORTS-1:0]  commit_instr_o,
    input  logic              [NR_COMMIT_PORTS-1:0]  commit_ack_i,

    output logic                                     stall_issue_o, // Used in Performance Counters

    //RVFI
    input [riscv::VLEN-1:0]                          lsu_addr_i,
    input [(riscv::XLEN/8)-1:0]                      lsu_rmask_i,
    input [(riscv::XLEN/8)-1:0]                      lsu_wmask_i,
    input [ariane_pkg::TRANS_ID_BITS-1:0]            lsu_addr_trans_id_i
);
    // ---------------------------------------------------
    // Scoreboard (SB) <-> Issue and Read Operands (IRO)
    // ---------------------------------------------------
    fu_t  [2**REG_ADDR_SIZE-1:0] rd_clobber_gpr_sb_iro;
    fu_t  [2**REG_ADDR_SIZE-1:0] rd_clobber_fpr_sb_iro;

    logic [REG_ADDR_SIZE-1:0]  rs1_iro_sb;
    riscv::xlen_t              rs1_sb_iro;
    logic                      rs1_valid_sb_iro;

    logic [REG_ADDR_SIZE-1:0]  rs2_iro_sb;
    riscv::xlen_t              rs2_sb_iro;
    logic                      rs2_valid_iro_sb;

    logic [REG_ADDR_SIZE-1:0]  rs3_iro_sb;
    rs3_len_t                  rs3_sb_iro;
    logic                      rs3_valid_iro_sb;

    scoreboard_entry_t         issue_instr_rename_sb;
    logic                      issue_instr_valid_rename_sb;
    logic                      issue_ack_sb_rename;

    scoreboard_entry_t         issue_instr_sb_iro;
    logic                      issue_instr_valid_sb_iro;
    logic                      issue_ack_iro_sb;

    riscv::xlen_t              rs1_forwarding_xlen;
    riscv::xlen_t              rs2_forwarding_xlen;

    assign rs1_forwarding_o = rs1_forwarding_xlen[riscv::VLEN-1:0];
    assign rs2_forwarding_o = rs2_forwarding_xlen[riscv::VLEN-1:0];

    // ---------------------------------------------------------
    // 1. Re-name
    // ---------------------------------------------------------
    re_name i_re_name (
        .clk_i                  ( clk_i                        ),
        .rst_ni                 ( rst_ni                       ),
        .flush_i                ( flush_i                      ),
        .flush_unissied_instr_i ( flush_unissued_instr_i       ),
        .issue_instr_i          ( decoded_instr_i              ),
        .issue_instr_valid_i    ( decoded_instr_valid_i        ),
        .issue_ack_o            ( decoded_instr_ack_o          ),
        .issue_instr_o          ( issue_instr_rename_sb        ),
        .issue_instr_valid_o    ( issue_instr_valid_rename_sb  ),
        .issue_ack_i            ( issue_ack_sb_rename          )
    );

    // ---------------------------------------------------------
    // 2. Manage instructions in a scoreboard
    // ---------------------------------------------------------
    scoreboard #(
        .NR_ENTRIES (NR_ENTRIES ),
        .NR_WB_PORTS(NR_WB_PORTS),
        .NR_COMMIT_PORTS(NR_COMMIT_PORTS)
    ) i_scoreboard (
        .sb_full_o             ( sb_full_o                                 ),
        .unresolved_branch_i   ( 1'b0                                      ),
        .rd_clobber_gpr_o      ( rd_clobber_gpr_sb_iro                     ),
        .rd_clobber_fpr_o      ( rd_clobber_fpr_sb_iro                     ),
        .rs1_i                 ( rs1_iro_sb                                ),
        .rs1_o                 ( rs1_sb_iro                                ),
        .rs1_valid_o           ( rs1_valid_sb_iro                          ),
        .rs2_i                 ( rs2_iro_sb                                ),
        .rs2_o                 ( rs2_sb_iro                                ),
        .rs2_valid_o           ( rs2_valid_iro_sb                          ),
        .rs3_i                 ( rs3_iro_sb                                ),
        .rs3_o                 ( rs3_sb_iro                                ),
        .rs3_valid_o           ( rs3_valid_iro_sb                          ),

        .decoded_instr_i       ( issue_instr_rename_sb                     ),
        .decoded_instr_valid_i ( issue_instr_valid_rename_sb               ),
        .decoded_instr_ack_o   ( issue_ack_sb_rename                       ),
        .issue_instr_o         ( issue_instr_sb_iro                        ),
        .issue_instr_valid_o   ( issue_instr_valid_sb_iro                  ),
        .issue_ack_i           ( issue_ack_iro_sb                          ),

        .resolved_branch_i     ( resolved_branch_i                         ),
        .trans_id_i            ( trans_id_i                                ),
        .wbdata_i              ( wbdata_i                                  ),
        .ex_i                  ( ex_ex_i                                   ),
        .lsu_addr_i            ( lsu_addr_i                                ),
        .lsu_rmask_i           ( lsu_rmask_i                               ),
        .lsu_wmask_i           ( lsu_wmask_i                               ),
        .lsu_addr_trans_id_i   ( lsu_addr_trans_id_i                       ),
        .rs1_forwarding_i      ( rs1_forwarding_xlen                       ),
        .rs2_forwarding_i      ( rs2_forwarding_xlen                       ),
        .*
    );

    // ---------------------------------------------------------
    // 3. Issue instruction and read operand, also commit
    // ---------------------------------------------------------
    issue_read_operands #(
      .NR_COMMIT_PORTS ( NR_COMMIT_PORTS )
    )i_issue_read_operands  (
        .flush_i             ( flush_unissued_instr_i          ),
        .issue_instr_i       ( issue_instr_sb_iro              ),
        .issue_instr_valid_i ( issue_instr_valid_sb_iro        ),
        .issue_ack_o         ( issue_ack_iro_sb                ),
        .fu_data_o           ( fu_data_o                       ),
        .flu_ready_i         ( flu_ready_i                     ),
        .rs1_o               ( rs1_iro_sb                      ),
        .rs1_i               ( rs1_sb_iro                      ),
        .rs1_valid_i         ( rs1_valid_sb_iro                ),
        .rs2_o               ( rs2_iro_sb                      ),
        .rs2_i               ( rs2_sb_iro                      ),
        .rs2_valid_i         ( rs2_valid_iro_sb                ),
        .rs3_o               ( rs3_iro_sb                      ),
        .rs3_i               ( rs3_sb_iro                      ),
        .rs3_valid_i         ( rs3_valid_iro_sb                ),
        .rd_clobber_gpr_i    ( rd_clobber_gpr_sb_iro           ),
        .rd_clobber_fpr_i    ( rd_clobber_fpr_sb_iro           ),
        .alu_valid_o         ( alu_valid_o                     ),
        .branch_valid_o      ( branch_valid_o                  ),
        .csr_valid_o         ( csr_valid_o                     ),
        .cvxif_valid_o       ( x_issue_valid_o                 ),
        .cvxif_ready_i       ( x_issue_ready_i                 ),
        .cvxif_off_instr_o   ( x_off_instr_o                   ),
        .mult_valid_o        ( mult_valid_o                    ),
        .rs1_forwarding_o    ( rs1_forwarding_xlen             ),
        .rs2_forwarding_o    ( rs2_forwarding_xlen             ),
        .stall_issue_o       ( stall_issue_o                   ),
        .*
    );

endmodule
