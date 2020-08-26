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


module issue_read_operands import ariane_pkg::*; #(
    parameter int unsigned NR_COMMIT_PORTS = 2
)(
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    // flush
    input  logic                                   flush_i,
    // coming from rename
    input  scoreboard_entry_t                      issue_instr_i,
    input  logic                                   issue_instr_valid_i,
    output logic                                   issue_ack_o,
    // lookup rd in scoreboard
    output logic [REG_ADDR_SIZE-1:0]               rs1_o,
    input  logic [63:0]                            rs1_i,
    input  logic                                   rs1_valid_i,
    output logic [REG_ADDR_SIZE-1:0]               rs2_o,
    input  logic [63:0]                            rs2_i,
    input  logic                                   rs2_valid_i,
    output logic [REG_ADDR_SIZE-1:0]               rs3_o,
    input  logic [FLEN-1:0]                        rs3_i,
    input  logic                                   rs3_valid_i,
    // get clobber input
    input  fu_t [2**REG_ADDR_SIZE-1:0]             rd_clobber_gpr_i,
    input  fu_t [2**REG_ADDR_SIZE-1:0]             rd_clobber_fpr_i,
    // To FU, just single issue for now
    output fu_data_t                               fu_data_o,
    output logic [riscv::VLEN-1:0]                 pc_o,
    output logic                                   is_compressed_instr_o,
    // ALU 1
    input  logic                                   flu_ready_i,      // Fixed latency unit ready to accept a new request
    output logic                                   alu_valid_o,      // Output is valid
    // Branches and Jumps
    output logic                                   branch_valid_o,   // this is a valid branch instruction
    output branchpredict_sbe_t                     branch_predict_o,
    // LSU
    input  logic                                   lsu_ready_i,      // FU is ready
    output logic                                   lsu_valid_o,      // Output is valid
    // MULT
    output logic                                   mult_valid_o,     // Output is valid
    // FPU
    input  logic                                   fpu_ready_i,      // FU is ready
    output logic                                   fpu_valid_o,      // Output is valid
    output logic [1:0]                             fpu_fmt_o,        // FP fmt field from instr.
    output logic [2:0]                             fpu_rm_o,         // FP rm field from instr.
    // CSR
    output logic                                   csr_valid_o,      // Output is valid
    // commit port
    input  logic [NR_COMMIT_PORTS-1:0][4:0]        waddr_i,
    input  logic [NR_COMMIT_PORTS-1:0][63:0]       wdata_i,
    input  logic [NR_COMMIT_PORTS-1:0]             we_gpr_i,
    input  logic [NR_COMMIT_PORTS-1:0]             we_fpr_i
    // committing instruction instruction
    // from scoreboard
    // input  scoreboard_entry     commit_instr_i,
    // output logic                commit_ack_o
);
    logic stall;   // stall signal, we do not want to fetch any more entries
    logic fu_busy; // functional unit is busy
    logic [63:0] operand_a_regfile, operand_b_regfile;  // operands coming from regfile
    logic [FLEN-1:0] operand_c_regfile; // third operand only from fp regfile
    // output flipflop (ID <-> EX)
    logic [63:0] operand_a_n, operand_a_q,
                 operand_b_n, operand_b_q,
                 imm_n, imm_q;

    logic          alu_valid_q;
    logic         mult_valid_q;
    logic          fpu_valid_q;
    logic [1:0]      fpu_fmt_q;
    logic [2:0]       fpu_rm_q;
    logic          lsu_valid_q;
    logic          csr_valid_q;
    logic       branch_valid_q;

    logic [TRANS_ID_BITS-1:0] trans_id_n, trans_id_q;
    fu_op operator_n, operator_q; // operation to perform
    fu_t  fu_n,       fu_q; // functional unit to use

    // forwarding signals
    logic forward_rs1, forward_rs2, forward_rs3;

    // original instruction stored in tval
    riscv::instruction_t orig_instr;
    assign orig_instr = riscv::instruction_t'(issue_instr_i.ex.tval[31:0]);

    // ID <-> EX registers
    assign fu_data_o.operand_a = operand_a_q;
    assign fu_data_o.operand_b = operand_b_q;
    assign fu_data_o.fu        = fu_q;
    assign fu_data_o.operator  = operator_q;
    assign fu_data_o.trans_id  = trans_id_q;
    assign fu_data_o.imm       = imm_q;
    assign alu_valid_o         = alu_valid_q;
    assign branch_valid_o      = branch_valid_q;
    assign lsu_valid_o         = lsu_valid_q;
    assign csr_valid_o         = csr_valid_q;
    assign mult_valid_o        = mult_valid_q;
    assign fpu_valid_o         = fpu_valid_q;
    assign fpu_fmt_o           = fpu_fmt_q;
    assign fpu_rm_o            = fpu_rm_q;
    // ---------------
    // Issue Stage
    // ---------------

    // select the right busy signal
    // this obviously depends on the functional unit we need
    always_comb begin : unit_busy
        unique case (issue_instr_i.fu)
            NONE:
                fu_busy = 1'b0;
            ALU, CTRL_FLOW, CSR, MULT:
                fu_busy = ~flu_ready_i;
            FPU, FPU_VEC:
                fu_busy = ~fpu_ready_i;
            LOAD, STORE:
                fu_busy = ~lsu_ready_i;
            default:
                fu_busy = 1'b0;
        endcase
    end

    // ---------------
    // Register stage
    // ---------------
    // check that all operands are available, otherwise stall
    // forward corresponding register
    always_comb begin : operands_available
        stall = 1'b0;
        // operand forwarding signals
        forward_rs1 = 1'b0;
        forward_rs2 = 1'b0;
        forward_rs3 = 1'b0; // FPR only
        // poll the scoreboard for those values
        rs1_o = issue_instr_i.rs1;
        rs2_o = issue_instr_i.rs2;
        rs3_o = issue_instr_i.result[REG_ADDR_SIZE-1:0]; // rs3 is encoded in imm field

        // 0. check that we are not using the zimm type in RS1
        //    as this is an immediate we do not have to wait on anything here
        // 1. check if the source registers are clobbered --> check appropriate clobber list (gpr/fpr)
        // 2. poll the scoreboard
        if (!issue_instr_i.use_zimm && (is_rs1_fpr(issue_instr_i.op) ? rd_clobber_fpr_i[issue_instr_i.rs1] != NONE
                                                                     : rd_clobber_gpr_i[issue_instr_i.rs1] != NONE)) begin
            // check if the clobbering instruction is not a CSR instruction, CSR instructions can only
            // be fetched through the register file since they can't be forwarded
            // if the operand is available, forward it. CSRs don't write to/from FPR
            if (rs1_valid_i && (is_rs1_fpr(issue_instr_i.op) ? 1'b1 : rd_clobber_gpr_i[issue_instr_i.rs1] != CSR)) begin
                forward_rs1 = 1'b1;
            end else begin // the operand is not available -> stall
                stall = 1'b1;
            end
        end

        if (is_rs2_fpr(issue_instr_i.op) ? rd_clobber_fpr_i[issue_instr_i.rs2] != NONE
                                         : rd_clobber_gpr_i[issue_instr_i.rs2] != NONE) begin
            // if the operand is available, forward it. CSRs don't write to/from FPR
            if (rs2_valid_i && (is_rs2_fpr(issue_instr_i.op) ? 1'b1 : rd_clobber_gpr_i[issue_instr_i.rs2] != CSR)) begin
                forward_rs2 = 1'b1;
            end else begin // the operand is not available -> stall
                stall = 1'b1;
            end
        end

        if (is_imm_fpr(issue_instr_i.op) && rd_clobber_fpr_i[issue_instr_i.result[REG_ADDR_SIZE-1:0]] != NONE) begin
            // if the operand is available, forward it. CSRs don't write to/from FPR so no need to check
            if (rs3_valid_i) begin
                forward_rs3 = 1'b1;
            end else begin // the operand is not available -> stall
                stall = 1'b1;
            end
        end
    end

    // Forwarding/Output MUX
    always_comb begin : forwarding_operand_select
        // default is regfiles (gpr or fpr)
        operand_a_n = operand_a_regfile;
        operand_b_n = operand_b_regfile;
        // immediates are the third operands in the store case
        // for FP operations, the imm field can also be the third operand from the regfile
        imm_n      = is_imm_fpr(issue_instr_i.op) ? operand_c_regfile : issue_instr_i.result;
        trans_id_n = issue_instr_i.trans_id;
        fu_n       = issue_instr_i.fu;
        operator_n = issue_instr_i.op;
        // or should we forward
        if (forward_rs1) begin
            operand_a_n  = rs1_i;
        end

        if (forward_rs2) begin
            operand_b_n  = rs2_i;
        end

        if (forward_rs3) begin
            imm_n  = rs3_i;
        end

        // use the PC as operand a
        if (issue_instr_i.use_pc) begin
            operand_a_n = {{64-riscv::VLEN{issue_instr_i.pc[riscv::VLEN-1]}}, issue_instr_i.pc};
        end

        // use the zimm as operand a
        if (issue_instr_i.use_zimm) begin
            // zero extend operand a
            operand_a_n = {59'b0, issue_instr_i.rs1[4:0]};
        end
        // or is it an immediate (including PC), this is not the case for a store and control flow instructions
        // also make sure operand B is not already used as an FP operand
        if (issue_instr_i.use_imm && (issue_instr_i.fu != STORE) && (issue_instr_i.fu != CTRL_FLOW) && !is_rs2_fpr(issue_instr_i.op)) begin
            operand_b_n = issue_instr_i.result;
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
        alu_valid_q    <= 1'b0;
        lsu_valid_q    <= 1'b0;
        mult_valid_q   <= 1'b0;
        fpu_valid_q    <= 1'b0;
        fpu_fmt_q      <= 2'b0;
        fpu_rm_q       <= 3'b0;
        csr_valid_q    <= 1'b0;
        branch_valid_q <= 1'b0;
        // Exception pass through:
        // If an exception has occurred simply pass it through
        // we do not want to issue this instruction
        if (!issue_instr_i.ex.valid && issue_instr_valid_i && issue_ack_o) begin
            case (issue_instr_i.fu)
                ALU:
                    alu_valid_q    <= 1'b1;
                CTRL_FLOW:
                    branch_valid_q <= 1'b1;
                MULT:
                    mult_valid_q   <= 1'b1;
                FPU : begin
                    fpu_valid_q    <= 1'b1;
                    fpu_fmt_q      <= orig_instr.rftype.fmt; // fmt bits from instruction
                    fpu_rm_q       <= orig_instr.rftype.rm;  // rm bits from instruction
                end
                FPU_VEC : begin
                    fpu_valid_q    <= 1'b1;
                    fpu_fmt_q      <= orig_instr.rvftype.vfmt;         // vfmt bits from instruction
                    fpu_rm_q       <= {2'b0, orig_instr.rvftype.repl}; // repl bit from instruction
                end
                LOAD, STORE:
                    lsu_valid_q    <= 1'b1;
                CSR:
                    csr_valid_q    <= 1'b1;
                default:;
            endcase
        end
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
        issue_ack_o = 1'b0;
        // check that we didn't stall, that the instruction we got is valid
        // and that the functional unit we need is not busy
        if (issue_instr_valid_i) begin
            // check that the corresponding functional unit is not busy
            if (!stall && !fu_busy) begin
                // -----------------------------------------
                // WAW - Write After Write Dependency Check
                // -----------------------------------------
                // no other instruction has the same destination register -> issue the instruction
                if (is_rd_fpr(issue_instr_i.op) ? (rd_clobber_fpr_i[issue_instr_i.rd] == NONE)
                                                : (rd_clobber_gpr_i[issue_instr_i.rd] == NONE)) begin
                    issue_ack_o = 1'b1;
                end
                // or check that the target destination register will be written in this cycle by the
                // commit stage
                for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++)
                    if (is_rd_fpr(issue_instr_i.op) ? (we_fpr_i[i] && waddr_i[i] == issue_instr_i.rd)
                                                    : (we_gpr_i[i] && waddr_i[i] == issue_instr_i.rd)) begin
                        issue_ack_o = 1'b1;
                    end
            end
            // we can also issue the instruction under the following two circumstances:
            // we can do this even if we are stalled or no functional unit is ready (as we don't need one)
            // the decoder needs to make sure that the instruction is marked as valid when it does not
            // need any functional unit or if an exception occurred previous to the execute stage.
            // 1. we already got an exception
            if (issue_instr_i.ex.valid) begin
                issue_ack_o = 1'b1;
            end
            // 2. it is an instruction which does not need any functional unit
            if (issue_instr_i.fu == NONE) begin
                issue_ack_o = 1'b1;
            end
        end
        // after a multiplication was issued we can only issue another multiplication
        // otherwise we will get contentions on the fixed latency bus
        if (mult_valid_q && issue_instr_i.fu != MULT) begin
            issue_ack_o = 1'b0;
        end
    end

    // ----------------------
    // Integer Register File
    // ----------------------
    logic [1:0][63:0] rdata;
    logic [1:0][4:0]  raddr_pack;

    // pack signals
    logic [NR_COMMIT_PORTS-1:0][4:0]  waddr_pack;
    logic [NR_COMMIT_PORTS-1:0][63:0] wdata_pack;
    logic [NR_COMMIT_PORTS-1:0]       we_pack;
    assign raddr_pack = {issue_instr_i.rs2[4:0], issue_instr_i.rs1[4:0]};
    for (genvar i = 0; i < NR_COMMIT_PORTS; i++) begin : gen_write_back_port
        assign waddr_pack[i] = waddr_i[i];
        assign wdata_pack[i] = wdata_i[i];
        assign we_pack[i]    = we_gpr_i[i];
    end

    ariane_regfile #(
        .DATA_WIDTH     ( 64              ),
        .NR_READ_PORTS  ( 2               ),
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
    logic [2:0][FLEN-1:0] fprdata;

    // pack signals
    logic [2:0][4:0]  fp_raddr_pack;
    logic [NR_COMMIT_PORTS-1:0][63:0] fp_wdata_pack;

    generate
        if (FP_PRESENT) begin : float_regfile_gen
            assign fp_raddr_pack = {issue_instr_i.result[4:0], issue_instr_i.rs2[4:0], issue_instr_i.rs1[4:0]};
            for (genvar i = 0; i < NR_COMMIT_PORTS; i++) begin : gen_fp_wdata_pack
                assign fp_wdata_pack[i] = {wdata_i[i][FLEN-1:0]};
            end

            ariane_regfile #(
                .DATA_WIDTH     ( FLEN            ),
                .NR_READ_PORTS  ( 3               ),
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

    assign operand_a_regfile = is_rs1_fpr(issue_instr_i.op) ? fprdata[0] : rdata[0];
    assign operand_b_regfile = is_rs2_fpr(issue_instr_i.op) ? fprdata[1] : rdata[1];
    assign operand_c_regfile = fprdata[2];

    // ----------------------
    // Registers (ID <-> EX)
    // ----------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            operand_a_q           <= '{default: 0};
            operand_b_q           <= '{default: 0};
            imm_q                 <= '0;
            fu_q                  <= NONE;
            operator_q            <= ADD;
            trans_id_q            <= '0;
            pc_o                  <= '0;
            is_compressed_instr_o <= 1'b0;
            branch_predict_o      <= {cf_t'(0), 64'd0};
        end else begin
            operand_a_q           <= operand_a_n;
            operand_b_q           <= operand_b_n;
            imm_q                 <= imm_n;
            fu_q                  <= fu_n;
            operator_q            <= operator_n;
            trans_id_q            <= trans_id_n;
            pc_o                  <= issue_instr_i.pc;
            is_compressed_instr_o <= issue_instr_i.is_compressed;
            branch_predict_o      <= issue_instr_i.bp;
        end
    end

    //pragma translate_off
    `ifndef VERILATOR
     assert property (
        @(posedge clk_i) (branch_valid_q) |-> (!$isunknown(operand_a_q) && !$isunknown(operand_b_q)))
        else $warning ("Got unknown value in one of the operands");

    `endif
    //pragma translate_on
endmodule


