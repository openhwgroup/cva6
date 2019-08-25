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
// Description: Issues instruction from the scoreboard and fetches the operands
//              This also includes all the forwarding logic

import ariane_pkg::*;

module issue_read_operands #(
    parameter int unsigned NR_COMMIT_PORTS = 2
)(
    input  logic                                      clk_i,    // Clock
    input  logic                                      rst_ni,   // Asynchronous reset active low
    // flush
    input  logic                                      flush_i,
    // coming from rename
    input  scoreboard_entry_t [ISSUE_WIDTH-1:0]       issue_instr_i,
    input  logic [ISSUE_WIDTH-1:0]                    issue_instr_valid_i,
    output logic [ISSUE_WIDTH-1:0]                    issue_ack_o,
    // lookup rd in scoreboard
    output logic [ISSUE_WIDTH-1:0][REG_ADDR_SIZE-1:0] rs1_o,
    input  logic [ISSUE_WIDTH-1:0][63:0]              rs1_i,
    input  logic [ISSUE_WIDTH-1:0]                    rs1_valid_i,
    output logic [ISSUE_WIDTH-1:0][REG_ADDR_SIZE-1:0] rs2_o,
    input  logic [ISSUE_WIDTH-1:0][63:0]              rs2_i,
    input  logic [ISSUE_WIDTH-1:0]                    rs2_valid_i,
    output logic [ISSUE_WIDTH-1:0][REG_ADDR_SIZE-1:0] rs3_o,
    input  logic [ISSUE_WIDTH-1:0][FLEN-1:0]          rs3_i,
    input  logic [ISSUE_WIDTH-1:0]                    rs3_valid_i,
    // get clobber input
    input  fu_t [2**REG_ADDR_SIZE-1:0]                rd_clobber_gpr_i,
    input  fu_t [2**REG_ADDR_SIZE-1:0]                rd_clobber_fpr_i,
    // To FU, just single issue for now
    output logic [63:0]                               pc_o,
    output logic                                      is_compressed_instr_o,
    output fu_data_t [ISSUE_WIDTH-1:0]                fu_data_o,
    // ALU
    input  logic [NR_FLU-1:0]                         flu_ready_i,      // Fixed latency unit ready to accept a new request
    output logic [NR_ALU-1:0]                         alu_valid_o,      // Output is valid
    output logic [NR_ALU-1:0][ISSUE_WIDTH_BITS-1:0]   alu_fu_idx_o,
    // Branches and Jumps
    output logic                                      branch_valid_o,   // this is a valid branch instruction
    output branchpredict_sbe_t                        branch_predict_o,
    output logic [ISSUE_WIDTH_BITS-1:0]               branch_fu_idx_o,
    // LSU
    input  logic                                      lsu_ready_i,      // FU is ready
    output logic                                      lsu_valid_o,      // Output is valid
    output logic [ISSUE_WIDTH_BITS-1:0]               lsu_fu_idx_o,
    // MULT
    output logic                                      mult_valid_o,     // Output is valid
    output logic                                      mult_fu_idx_o,
    // FPU
    input  logic                                      fpu_ready_i,      // FU is ready
    output logic                                      fpu_valid_o,      // Output is valid
    output logic [ISSUE_WIDTH_BITS-1:0]               fpu_fu_idx_o,
    output logic [1:0]                                fpu_fmt_o,        // FP fmt field from instr.
    output logic [2:0]                                fpu_rm_o,         // FP rm field from instr.
    // CSR
    output logic                                      csr_valid_o,      // Output is valid
    output logic [ISSUE_WIDTH_BITS-1:0]               csr_fu_idx_o,
    // commit port
    input  logic [NR_COMMIT_PORTS-1:0][4:0]           waddr_i,
    input  logic [NR_COMMIT_PORTS-1:0][63:0]          wdata_i,
    input  logic [NR_COMMIT_PORTS-1:0]                we_gpr_i,
    input  logic [NR_COMMIT_PORTS-1:0]                we_fpr_i
    // committing instruction instruction
    // from scoreboard
    // input  scoreboard_entry     commit_instr_i,
    // output logic                commit_ack_o
);
    logic [ISSUE_WIDTH-1:0] stall;   // stall signal, we do not want to fetch any more entries
    logic [ISSUE_WIDTH-1:0] fu_busy; // functional unit is busy
    logic [ISSUE_WIDTH-1:0][63:0] operand_a_regfile, operand_b_regfile;  // operands coming from regfile
    logic [ISSUE_WIDTH-1:0][FLEN-1:0] operand_c_regfile; // third operand only from fp regfile
    // output flipflop (ID <-> EX)
    logic [ISSUE_WIDTH-1:0][63:0] operand_a_n, operand_b_n, imm_n;

    // record if any function unit is busy in the same issue cycle
    logic [NR_FLU-1:0]  flu_busy;
    logic               fpu_busy, ls_busy;
    logic               cf_exist;
    logic [ISSUE_WIDTH-1:0][NR_ALU-1:0] alu_sel; // record which ALU to use

    logic [NR_ALU-1:0]   alu_valid_n, alu_valid_q;
    logic                mult_valid_n, mult_valid_q;
    logic                fpu_valid_n, fpu_valid_q;
    logic [1:0]          fpu_fmt_n, fpu_fmt_q;
    logic [2:0]          fpu_rm_n, fpu_rm_q;
    logic                lsu_valid_n, lsu_valid_q;
    logic                csr_valid_n, csr_valid_q;
    logic                branch_valid_n, branch_valid_q;

    logic [NR_ALU-1:0][ISSUE_WIDTH_BITS-1:0] alu_fu_idx_n, alu_fu_idx_q;
    logic [ISSUE_WIDTH_BITS-1:0]             branch_fu_idx_n, branch_fu_idx_q;
    logic [ISSUE_WIDTH_BITS-1:0]             csr_fu_idx_n, csr_fu_idx_q;
    logic [ISSUE_WIDTH_BITS-1:0]             mult_fu_idx_n, mult_fu_idx_q;
    logic [ISSUE_WIDTH_BITS-1:0]             fpu_fu_idx_n, fpu_fu_idx_q;
    logic [ISSUE_WIDTH_BITS-1:0]             lsu_fu_idx_n, lsu_fu_idx_q;

    logic [ISSUE_WIDTH-1:0][TRANS_ID_BITS-1:0] trans_id_n;
    fu_op [ISSUE_WIDTH-1:0] operator_n; // operation to perform
    fu_t  [ISSUE_WIDTH-1:0] fu_n;       // functional unit to use
    logic [63:0] pc_n, pc_q;
    logic is_compressed_instr_n, is_compressed_instr_q;
    branchpredict_sbe_t branch_predict_n, branch_predict_q;
    fu_data_t [ISSUE_WIDTH-1:0] fu_data_n, fu_data_q;

    // forwarding signals
    logic [ISSUE_WIDTH-1:0] forward_rs1, forward_rs2, forward_rs3;

    // original instruction stored in tval
    riscv::instruction_t orig_instr;

    // if the rd is hold by other instructions in the same issue
    ariane_pkg::fu_t [ISSUE_WIDTH-1:0][2**ariane_pkg::REG_ADDR_SIZE-1:0] rd_issue_clobber_gpr, rd_issue_clobber_fpr;

    // ID <-> EX registers
    assign fu_data_o           = fu_data_q;
    assign alu_valid_o         = alu_valid_q;
    assign branch_valid_o      = branch_valid_q;
    assign lsu_valid_o         = lsu_valid_q;
    assign csr_valid_o         = csr_valid_q;
    assign mult_valid_o        = mult_valid_q;
    assign fpu_valid_o         = fpu_valid_q;
    assign fpu_fmt_o           = fpu_fmt_q;
    assign fpu_rm_o            = fpu_rm_q;
    assign pc_o                = pc_q;
    assign is_compressed_instr_o = is_compressed_instr_q;
    assign branch_predict_o = branch_predict_q;

    assign alu_fu_idx_o    = alu_fu_idx_q;
    assign mult_fu_idx_o   = mult_fu_idx_q;
    assign csr_fu_idx_o    = csr_fu_idx_q;
    assign lsu_fu_idx_o    = lsu_fu_idx_q;
    assign fpu_fu_idx_o    = fpu_fu_idx_q;
    assign branch_fu_idx_o = branch_fu_idx_q;

    for (genvar i = 0; i < ISSUE_WIDTH; i++) begin
        assign fu_data_n[i].operand_a = operand_a_n[i];
        assign fu_data_n[i].operand_b = operand_b_n[i];
        assign fu_data_n[i].fu        = fu_n[i];
        assign fu_data_n[i].operator  = operator_n[i];
        assign fu_data_n[i].trans_id  = trans_id_n[i];
        assign fu_data_n[i].imm       = imm_n[i];
    end

    // ---------------
    // Issue Stage
    // ---------------

    // select the right busy signal
    // this obviously depends on the functional unit we need
    // currently we have two FLU ports. First one for multiplier and one ALU
    // and second one for branch unit, csr and the other ALU
    always_comb begin : unit_busy
        flu_busy     = '0;
        fpu_busy     = 1'b0;
        ls_busy      = 1'b0;
        fu_busy      = '0;
        alu_sel      = '{default: 0};
        cf_exist     = 1'b0;

        for (int unsigned i = 0; i < ISSUE_WIDTH; i++) begin

            // Hold the exception instruction until the branch is solved
            if (cf_exist && issue_instr_i[i].ex.valid && issue_instr_valid_i[i]) begin
                fu_busy[i] = 1'b1;
            end

            unique case (issue_instr_i[i].fu)
                NONE:
                    fu_busy[i] = 1'b0;
                ALU: begin
                    if (flu_ready_i[0] & ~flu_busy[0]) begin
                        flu_busy[0] = 1'b1;
                        alu_sel[i][0] = 1'b1;
                    end else if (flu_ready_i[1] & ~flu_busy[1]) begin
                        flu_busy[1] = 1'b1;
                        alu_sel[i][1] = 1'b1;
                    end else begin
                        fu_busy[i] = 1'b1;
                    end
                end
                MULT: begin
                    fu_busy[i] = ~flu_ready_i[0] | flu_busy[0];
                    flu_busy[0] = 1'b1;
                end
                CTRL_FLOW: begin
                    fu_busy[i] = ~flu_ready_i[1] | flu_busy[1];
                    flu_busy[1] = 1'b1;
                    cf_exist = ~fu_busy;
                end
                CSR: begin
                    fu_busy[i] = ~flu_ready_i[1] | flu_busy[1];
                    flu_busy[1] = 1'b1;
                end
                FPU, FPU_VEC: begin
                    fu_busy[i] = ~fpu_ready_i | fpu_busy;
                    fpu_busy = 1'b1;
                end
                LOAD, STORE: begin
                    fu_busy[i] = ~lsu_ready_i | ls_busy;
                    ls_busy = 1'b1;
                end
                default:
                    fu_busy[i] = 1'b0;
            endcase
        end
    end

    // check whether other instructions on the same cycle holding the rd
    always_comb begin
        for (int unsigned i = 0; i < ISSUE_WIDTH; i++) begin
            for (int unsigned j = 0; j < 2**ariane_pkg::REG_ADDR_SIZE; j++) begin
                rd_issue_clobber_gpr[i][j] = ariane_pkg::NONE;
                rd_issue_clobber_fpr[i][j] = ariane_pkg::NONE;
            end
        end

        for (int unsigned i = 0; i < ISSUE_WIDTH; i++) begin
            if (!issue_instr_i[i].ex.valid && issue_instr_valid_i[i]) begin
                for (int unsigned j = (i+1); j < ISSUE_WIDTH; j++) begin
                    if (is_rd_fpr(issue_instr_i[i].op))
                        rd_issue_clobber_fpr[j][issue_instr_i[i].rd] = issue_instr_i[i].fu;
                    else
                        rd_issue_clobber_gpr[j][issue_instr_i[i].rd] = issue_instr_i[i].fu;
                end
            end
        end
    end

    always_comb begin
        alu_valid_n    = '0;
        lsu_valid_n    = 1'b0;
        mult_valid_n   = 1'b0;
        fpu_valid_n    = 1'b0;
        fpu_fmt_n      = 2'b0;
        fpu_rm_n       = 3'b0;
        csr_valid_n    = 1'b0;
        branch_valid_n = 1'b0;

        pc_n = '0;
        branch_predict_n = '{default: 0};
        is_compressed_instr_n = 1'b0;

        alu_fu_idx_n    = '{default: 0};
        branch_fu_idx_n = '0;
        mult_fu_idx_n   = '0;
        fpu_fu_idx_n    = '0;
        mult_fu_idx_n   = '0;
        csr_fu_idx_n    = '0;

        // front instructions get higher prio
        for (int unsigned i = 0; i < ISSUE_WIDTH; i++) begin
            // original instruction stored in tval
            orig_instr = riscv::instruction_t'(issue_instr_i[i].ex.tval[31:0]);

            // Exception pass through:
            // If an exception has occurred simply pass it through
            // we do not want to issue this instruction
            if (!issue_instr_i[i].ex.valid && issue_instr_valid_i[i] && issue_ack_o[i]) begin
                case (issue_instr_i[i].fu)
                    ALU: begin
                        if (alu_sel[i][0]) begin
                            alu_valid_n[0] = 1'b1;
                            alu_fu_idx_n[0] = i;
                        end else if (alu_sel[i][1]) begin
                            alu_valid_n[1] = 1'b1;
                            alu_fu_idx_n[1] = i;
                        end
                    end
                    CTRL_FLOW: begin
                        branch_valid_n         = 1'b1;
                        pc_n                   = issue_instr_i[i].pc;
                        branch_predict_n       = issue_instr_i[i].bp;
                        is_compressed_instr_n  = issue_instr_i[i].is_compressed;
                        branch_fu_idx_n        = i;
                    end
                    MULT: begin
                        mult_valid_n           = 1'b1;
                        mult_fu_idx_n          = i;
                    end
                    FPU : begin
                        fpu_valid_n           = 1'b1;
                        fpu_fmt_n             = orig_instr.rftype.fmt; // fmt bits from instruction
                        fpu_rm_n              = orig_instr.rftype.rm;  // rm bits from instruction
                        fpu_fu_idx_n          = i;
                    end
                    FPU_VEC : begin
                        fpu_valid_n           = 1'b1;
                        fpu_fmt_n             = orig_instr.rvftype.vfmt;         // vfmt bits from instruction
                        fpu_rm_n              = {2'b0, orig_instr.rvftype.repl}; // repl bit from instruction
                        fpu_fu_idx_n          = i;
                    end
                    LOAD, STORE: begin
                        lsu_valid_n           = 1'b1;
                        lsu_fu_idx_n          = i;
                    end
                    CSR: begin
                        csr_valid_n           = 1'b1;
                        csr_fu_idx_n          = i;
                    end
                    default:;
                endcase
            end
        end
    end
    // ---------------
    // Register stage
    // ---------------
    // check that all operands are available, otherwise stall
    // forward corresponding register
    always_comb begin : operands_available
        stall = '0;
        for (int unsigned i = 0; i < ISSUE_WIDTH; i++) begin
            // operand forwarding signals
            forward_rs1[i] = 1'b0;
            forward_rs2[i] = 1'b0;
            forward_rs3[i] = 1'b0; // FPR only
            // poll the scoreboard for those values
            rs1_o[i] = issue_instr_i[i].rs1;
            rs2_o[i] = issue_instr_i[i].rs2;
            rs3_o[i] = issue_instr_i[i].result[REG_ADDR_SIZE-1:0]; // rs3 is encoded in imm field

            // stall if instructions ahead in the issue cycle hold the operand
            if (!issue_instr_i[i].use_zimm
                && (is_rs1_fpr(issue_instr_i[i].op) ? rd_issue_clobber_fpr[i][issue_instr_i[i].rs1] != NONE
                                                    : rd_issue_clobber_gpr[i][issue_instr_i[i].rs1] != NONE)) begin
                stall[i] = 1'b1;
            end

            if (is_rs2_fpr(issue_instr_i[i].op) ? rd_issue_clobber_fpr[i][issue_instr_i[i].rs2] != NONE
                                                : rd_issue_clobber_gpr[i][issue_instr_i[i].rs2] != NONE) begin
                stall[i] = 1'b1;
            end

            if (is_imm_fpr(issue_instr_i[i].op) && rd_issue_clobber_fpr[i][issue_instr_i[i].result[REG_ADDR_SIZE-1:0]] != NONE) begin
                stall[i] = 1'b1;
            end

            // 0. check that we are not using the zimm type in RS1
            //    as this is an immediate we do not have to wait on anything here
            // 1. check if the source registers are clobbered --> check appropriate clobber list (gpr/fpr)
            // 2. poll the scoreboard
            if (!issue_instr_i[i].use_zimm
                && (is_rs1_fpr(issue_instr_i[i].op) ? (rd_clobber_fpr_i[issue_instr_i[i].rs1] != NONE)
                                                    : (rd_clobber_gpr_i[issue_instr_i[i].rs1] != NONE))) begin
                // check if the clobbering instruction is not a CSR instruction, CSR instructions can only
                // be fetched through the register file since they can't be forwarded
                // if the operand is available, forward it. CSRs don't write to/from FPR
                if (rs1_valid_i[i] && (is_rs1_fpr(issue_instr_i[i].op) ? 1'b1 : (rd_clobber_gpr_i[issue_instr_i[i].rs1] != CSR))) begin
                    forward_rs1[i] = 1'b1;
                end else begin // the operand is not available -> stall
                    stall[i] = 1'b1;
                end
            end

            if (is_rs2_fpr(issue_instr_i[i].op) ? (rd_clobber_fpr_i[issue_instr_i[i].rs2] != NONE )
                                                : (rd_clobber_gpr_i[issue_instr_i[i].rs2] != NONE )) begin
                // if the operand is available, forward it. CSRs don't write to/from FPR
                if (rs2_valid_i[i]
                    && (is_rs2_fpr(issue_instr_i[i].op) ? 1'b1 : (rd_clobber_gpr_i[issue_instr_i[i].rs2] != CSR))
                ) begin
                    forward_rs2[i] = 1'b1;
                end else begin // the operand is not available -> stall
                    stall[i] = 1'b1;
                end
            end

            if (is_imm_fpr(issue_instr_i[i].op) && rd_clobber_fpr_i[issue_instr_i[i].result[REG_ADDR_SIZE-1:0]] != NONE) begin
                // if the operand is available, forward it. CSRs don't write to/from FPR so no need to check
                if (rs3_valid_i[i]) begin
                    forward_rs3[i] = 1'b1;
                end else begin // the operand is not available -> stall
                    stall[i] = 1'b1;
                end
            end
        end
    end

    // Forwarding/Output MUX
    always_comb begin : forwarding_operand_select
        for (int unsigned i = 0; i < ISSUE_WIDTH; i++) begin
            // default is regfiles (gpr or fpr)
            operand_a_n[i] = operand_a_regfile[i];
            operand_b_n[i] = operand_b_regfile[i];
            // immediates are the third operands in the store case
            // for FP operations, the imm field can also be the third operand from the regfile
            imm_n[i]      = is_imm_fpr(issue_instr_i[i].op) ? operand_c_regfile[i] : issue_instr_i[i].result;
            trans_id_n[i] = issue_instr_i[i].trans_id;
            fu_n[i]       = issue_instr_i[i].fu;
            operator_n[i] = issue_instr_i[i].op;
            // or should we forward
            if (forward_rs1[i]) begin
                operand_a_n[i]  = rs1_i[i];
            end

            if (forward_rs2[i]) begin
                operand_b_n[i]  = rs2_i[i];
            end

            if (forward_rs3[i]) begin
                imm_n[i]  = rs3_i[i];
            end

            // use the PC as operand a
            if (issue_instr_i[i].use_pc) begin
                operand_a_n[i] = issue_instr_i[i].pc;
            end

            // use the zimm as operand a
            if (issue_instr_i[i].use_zimm) begin
                // zero extend operand a
                operand_a_n[i] = {52'b0, issue_instr_i[i].rs1[4:0]};
            end
            // or is it an immediate (including PC), this is not the case for a store and control flow instructions
            // also make sure operand B is not already used as an FP operand
            if (issue_instr_i[i].use_imm && (issue_instr_i[i].fu != STORE) && (issue_instr_i[i].fu != CTRL_FLOW) && !is_rs2_fpr(issue_instr_i[i].op)) begin
                operand_b_n[i] = issue_instr_i[i].result;
            end
        end
    end

    // FU select, assert the correct valid out signal (in the next cycle)
    // This needs to be like this to make verilator happy. I know its ugly.
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            alu_valid_q    <= 1'b0;
            lsu_valid_q    <= 1'b0;
            mult_valid_q   <= 1'b0;
            fpu_valid_q    <= 1'b0;
            fpu_fmt_q      <= 2'b0;
            fpu_rm_q       <= 3'b0;
            csr_valid_q    <= 1'b0;
            branch_valid_q <= 1'b0;
        end else begin
            alu_valid_q    <= alu_valid_n;
            lsu_valid_q    <= lsu_valid_n;
            mult_valid_q   <= mult_valid_n;
            fpu_valid_q    <= fpu_valid_n;
            fpu_fmt_q      <= fpu_fmt_n;
            fpu_rm_q       <= fpu_rm_n;
            csr_valid_q    <= csr_valid_n;
            branch_valid_q <= branch_valid_n;
            // if we got a flush request, de-assert the valid flag, otherwise we will start this
            // functional unit with the wrong inputs
            if (flush_i) begin
                alu_valid_q    <= 1'b0;
                lsu_valid_q    <= 1'b0;
                mult_valid_q   <= 1'b0;
                fpu_valid_q    <= 1'b0;
                csr_valid_q    <= 1'b0;
                branch_valid_q <= 1'b0;
            end
        end
    end

    // We can issue an instruction if we do not detect that any other instruction is writing the same
    // destination register.
    // We also need to check if there is an unresolved branch in the scoreboard.
    always_comb begin : issue_scoreboard
        // default assignment
        issue_ack_o = '0;
        for (int unsigned i = 0; i < ISSUE_WIDTH; i++) begin
            // check that we didn't stall, that the instruction we got is valid
            // and that the functional unit we need is not busy
            if (issue_instr_valid_i[i]) begin
                // check that the corresponding functional unit is not busy
                if (!stall[i] && !fu_busy[i]) begin
                    // -----------------------------------------
                    // WAW - Write After Write Dependency Check
                    // -----------------------------------------
                    // no other instruction has the same destination register -> issue the instruction
                    if (is_rd_fpr(issue_instr_i[i].op) ? (rd_clobber_fpr_i[issue_instr_i[i].rd] == NONE) & (rd_issue_clobber_fpr[i][issue_instr_i[i].rd] == NONE)
                                                       : (rd_clobber_gpr_i[issue_instr_i[i].rd] == NONE) & (rd_issue_clobber_gpr[i][issue_instr_i[i].rd] == NONE)) begin
                        if (i == 0)
                          issue_ack_o[i] = 1'b1;
                        else
                          issue_ack_o[i] = issue_ack_o[i-1];
                    end
                    // or check that the target destination register will be written in this cycle by the
                    // commit stage
                    for (int unsigned j = 0; j < NR_COMMIT_PORTS; j++) begin
                        if (is_rd_fpr(issue_instr_i[i].op) ? (we_fpr_i[j] && waddr_i[j] == issue_instr_i[i].rd)
                                                           : (we_gpr_i[j] && waddr_i[j] == issue_instr_i[i].rd)) begin
                        if (i == 0)
                          issue_ack_o[i] = 1'b1;
                        else
                          issue_ack_o[i] = issue_ack_o[i-1];
                        end
                    end
                end
                // we can also issue the instruction under the following two circumstances:
                // we can do this even if we are stalled or no functional unit is ready (as we don't need one)
                // the decoder needs to make sure that the instruction is marked as valid when it does not
                // need any functional unit or if an exception occurred previous to the execute stage.
                // 1. we already got an exception
                if (issue_instr_i[i].ex.valid && !fu_busy[i]) begin
                    if (i == 0)
                      issue_ack_o[i] = 1'b1;
                    else
                      issue_ack_o[i] = issue_ack_o[i-1];
                end
                // 2. it is an instruction which does not need any functional unit
                if (issue_instr_i[i].fu == NONE) begin
                    if (i == 0)
                      issue_ack_o[i] = 1'b1;
                    else
                      issue_ack_o[i] = issue_ack_o[i-1];
                end
            end

            // after a multiplication was issued we can only issue another multiplication
            // otherwise we will get contentions on the fixed latency bus
            if (mult_valid_q && issue_instr_i[i].fu != MULT) begin
                issue_ack_o[i]= 1'b0;
            end
        end
    end

    // ----------------------
    // Integer Register File
    // ----------------------
    logic [2*ISSUE_WIDTH-1:0][63:0] rdata;
    logic [2*ISSUE_WIDTH-1:0][4:0]  raddr_pack;

    // pack signals
    logic [NR_COMMIT_PORTS-1:0][4:0]  waddr_pack;
    logic [NR_COMMIT_PORTS-1:0][63:0] wdata_pack;
    logic [NR_COMMIT_PORTS-1:0]       we_pack;

    for (genvar i = 0; i < ISSUE_WIDTH; i++) begin : gen_regfile_raddr
        assign raddr_pack[2*i]   = issue_instr_i[i].rs1[4:0];
        assign raddr_pack[2*i+1] = issue_instr_i[i].rs2[4:0];
    end
    assign waddr_pack = {waddr_i[1],  waddr_i[0]};
    assign wdata_pack = {wdata_i[1],  wdata_i[0]};
    assign we_pack    = {we_gpr_i[1], we_gpr_i[0]};
    ariane_regfile #(
        .DATA_WIDTH     ( 64              ),
        .NR_READ_PORTS  ( 2 * ISSUE_WIDTH ),
        .NR_WRITE_PORTS ( NR_COMMIT_PORTS ),
        .ZERO_REG_ZERO  ( 1               )
    ) i_ariane_regfile (
        .test_en_i ( 1'b0       ),
        .raddr_i   ( raddr_pack ),
        .rdata_o   ( rdata      ),
        .waddr_i   ( waddr_pack ),
        .wdata_i   ( wdata_pack ),
        .we_i      ( we_pack    ),
        .*
    );

    // -----------------------------
    // Floating-Point Register File
    // -----------------------------
    logic [3*ISSUE_WIDTH-1:0][FLEN-1:0] fprdata;

    // pack signals
    logic [3*ISSUE_WIDTH-1:0][4:0]    fp_raddr_pack;
    logic [NR_COMMIT_PORTS-1:0][63:0] fp_wdata_pack;

    generate
        if (FP_PRESENT) begin : float_regfile_gen
            for (genvar i = 0; i < ISSUE_WIDTH; i++) begin : gen_fp_regfile_raddr
                assign fp_raddr_pack[i*3]   = issue_instr_i[i].rs1[4:0];
                assign fp_raddr_pack[i*3+1] = issue_instr_i[i].rs2[4:0];
                assign fp_raddr_pack[i*3+2] = issue_instr_i[i].result[4:0];
            end
            assign fp_wdata_pack = {wdata_i[1][FLEN-1:0], wdata_i[0][FLEN-1:0]};

            ariane_regfile #(
                .DATA_WIDTH     ( FLEN            ),
                .NR_READ_PORTS  ( 3 * ISSUE_WIDTH ),
                .NR_WRITE_PORTS ( NR_COMMIT_PORTS ),
                .ZERO_REG_ZERO  ( 0               )
            ) i_ariane_fp_regfile (
                .test_en_i ( 1'b0          ),
                .raddr_i   ( fp_raddr_pack ),
                .rdata_o   ( fprdata       ),
                .waddr_i   ( waddr_pack    ),
                .wdata_i   ( wdata_pack    ),
                .we_i      ( we_fpr_i      ),
                .*
            );
        end else begin : no_fpr_gen
            assign fprdata = '{default: '0};
        end
    endgenerate

    for (genvar i = 0; i < ISSUE_WIDTH; i++) begin : gen_operand_regfile
        assign operand_a_regfile[i] = is_rs1_fpr(issue_instr_i[i].op) ? fprdata[3*i] : rdata[2*i];
        assign operand_b_regfile[i] = is_rs2_fpr(issue_instr_i[i].op) ? fprdata[3*i+1] : rdata[2*i+1];
        assign operand_c_regfile[i] = fprdata[3*i+1];
    end
    // ----------------------
    // Registers (ID <-> EX)
    // ----------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            pc_q                  <= '0;
            is_compressed_instr_q <= 1'b0;
            branch_predict_q      <= '{default: 0};
            fu_data_q             <= '{default: 0};
            alu_fu_idx_q          <= '{default: 0};
            branch_fu_idx_q       <= '0;
            fpu_fu_idx_q          <= '0;
            mult_fu_idx_q         <= '0;
            csr_fu_idx_q          <= '0;
            lsu_fu_idx_q          <= '0;
        end else begin
            pc_q                  <= pc_n;
            is_compressed_instr_q <= is_compressed_instr_n;
            branch_predict_q      <= branch_predict_n;
            fu_data_q             <= fu_data_n;
            alu_fu_idx_q          <= alu_fu_idx_n;
            branch_fu_idx_q       <= branch_fu_idx_n;
            fpu_fu_idx_q          <= fpu_fu_idx_n;
            mult_fu_idx_q         <= mult_fu_idx_n;
            csr_fu_idx_q          <= csr_fu_idx_n;
            lsu_fu_idx_q          <= lsu_fu_idx_n;
        end
    end

    //pragma translate_off
    `ifndef VERILATOR
     assert property (
        @(posedge clk_i) (branch_valid_q) |-> (!$isunknown(operand_a_q) && !$isunknown(operand_b_q)))
        else $warning ("Got unknown value in one of the operands");

    initial begin
        assert (NR_COMMIT_PORTS == 2) else $error("Only two commit ports are supported at the moment!");
    end
    `endif
    //pragma translate_on
endmodule


