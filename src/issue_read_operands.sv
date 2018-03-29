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
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    input  logic                                   test_en_i,
    // flush
    input  logic                                   flush_i,
    // coming from Debug
    input  logic                                   debug_gpr_req_i,
    input  logic [4:0]                             debug_gpr_addr_i,
    input  logic                                   debug_gpr_we_i,
    input  logic [63:0]                            debug_gpr_wdata_i,
    output logic [63:0]                            debug_gpr_rdata_o,
    // coming from scoreboard
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
    // get clobber input
    input  fu_t [2**REG_ADDR_SIZE:0]               rd_clobber_i,
    // To FU, just single issue for now
    output fu_t                                    fu_o,
    output fu_op                                   operator_o,
    output logic [63:0]                            operand_a_o,
    output logic [63:0]                            operand_b_o,
    output logic [63:0]                            imm_o,           // output immediate for the LSU
    output logic [TRANS_ID_BITS-1:0]               trans_id_o,
    output logic [63:0]                            pc_o,
    output logic                                   is_compressed_instr_o,
    // ALU 1
    input  logic                                   alu_ready_i,      // FU is ready
    output logic                                   alu_valid_o,      // Output is valid
    // Branches and Jumps
    input  logic                                   branch_ready_i,
    output logic                                   branch_valid_o,   // this is a valid branch instruction
    output branchpredict_sbe_t                     branch_predict_o,
    // LSU
    input  logic                                   lsu_ready_i,      // FU is ready
    output logic                                   lsu_valid_o,      // Output is valid
    // MULT
    input  logic                                   mult_ready_i,      // FU is ready
    output logic                                   mult_valid_o,      // Output is valid
    // CSR
    input  logic                                   csr_ready_i,      // FU is ready
    output logic                                   csr_valid_o,      // Output is valid
    // commit port
    input  logic [NR_COMMIT_PORTS-1:0][4:0]        waddr_i,
    input  logic [NR_COMMIT_PORTS-1:0][63:0]       wdata_i,
    input  logic [NR_COMMIT_PORTS-1:0]             we_i,
    input  logic [NR_COMMIT_PORTS-1:0]             we_fpr_i
    // committing instruction instruction
    // from scoreboard
    // input  scoreboard_entry     commit_instr_i,
    // output logic                commit_ack_o
);
    logic stall;   // stall signal, we do not want to fetch any more entries
    logic fu_busy; // functional unit is busy
    logic [63:0] operand_a_regfile, operand_b_regfile;  // operands coming from regfile

    // output flipflop (ID <-> EX)
    logic [63:0] operand_a_n, operand_a_q,
                 operand_b_n, operand_b_q,
                 imm_n, imm_q;

    logic alu_valid_n,    alu_valid_q;
    logic mult_valid_n,   mult_valid_q;
    logic lsu_valid_n,    lsu_valid_q;
    logic csr_valid_n,    csr_valid_q;
    logic branch_valid_n, branch_valid_q;

    logic [TRANS_ID_BITS-1:0] trans_id_n, trans_id_q;
    fu_op operator_n, operator_q; // operation to perform
    fu_t  fu_n,       fu_q; // functional unit to use

    // forwarding signals
    logic forward_rs1, forward_rs2;
    // ID <-> EX registers
    assign operand_a_o    = operand_a_q;
    assign operand_b_o    = operand_b_q;
    assign fu_o           = fu_q;
    assign operator_o     = operator_q;
    assign alu_valid_o    = alu_valid_q;
    assign branch_valid_o = branch_valid_q;
    assign lsu_valid_o    = lsu_valid_q;
    assign csr_valid_o    = csr_valid_q;
    assign mult_valid_o   = mult_valid_q;
    assign trans_id_o     = trans_id_q;
    assign imm_o          = imm_q;
    // ---------------
    // Issue Stage
    // ---------------
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
            if (~stall && ~fu_busy) begin
                // -----------------------------------------
                // WAW - Write After Write Dependency Check
                // -----------------------------------------
                // no other instruction has the same destination register -> issue the instruction
                if (rd_clobber_i[issue_instr_i.rd] == NONE) begin
                    issue_ack_o = 1'b1;
                end
                // or check that the target destination register will be written in this cycle by the
                // commit stage
                for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++)
                    if (we_i[i] && waddr_i[i] == issue_instr_i.rd) begin
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
    end

    // select the right busy signal
    // this obviously depends on the functional unit we need
    always_comb begin : unit_busy
        unique case (issue_instr_i.fu)
            NONE:
                fu_busy = 1'b0;
            ALU:
                fu_busy = ~alu_ready_i;
            CTRL_FLOW:
                fu_busy = ~branch_ready_i;
            MULT:
                fu_busy = ~mult_ready_i;
            LOAD, STORE:
                fu_busy = ~lsu_ready_i;
            CSR:
                fu_busy = ~csr_ready_i;
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
        // poll the scoreboard for those values
        rs1_o = issue_instr_i.rs1;
        rs2_o = issue_instr_i.rs2;
        // 0. check that we are not using the zimm type in RS1
        //    as this is an immediate we do not have to wait on anything here
        // 1. check if the source registers are clobberd
        // 2. poll the scoreboard
        if (~issue_instr_i.use_zimm && rd_clobber_i[issue_instr_i.rs1] != NONE) begin
            // check if the clobbering instruction is not a CSR instruction, CSR instructions can only
            // be fetched through the register file since they can't be forwarded
            // the operand is available, forward it
            if (rs1_valid_i && rd_clobber_i[issue_instr_i.rs1] != CSR)
                forward_rs1 = 1'b1;
            else // the operand is not available -> stall
                stall = 1'b1;

        end

        if (rd_clobber_i[issue_instr_i.rs2] != NONE) begin
            // the operand is available, forward it
            if (rs2_valid_i && rd_clobber_i[issue_instr_i.rs2] != CSR)
                forward_rs2 = 1'b1;
            else // the operand is not available -> stall
                stall = 1'b1;
        end
    end
    // Forwarding/Output MUX
    always_comb begin : forwarding_operand_select
        // default is regfile
        operand_a_n = operand_a_regfile;
        operand_b_n = operand_b_regfile;
        // immediates are the third operands in the store case
        imm_n      = issue_instr_i.result;
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

        // use the PC as operand a
        if (issue_instr_i.use_pc) begin
            operand_a_n = issue_instr_i.pc;
        end

        // use the zimm as operand a
        if (issue_instr_i.use_zimm) begin
            // zero extend operand a
            operand_a_n = {52'b0, issue_instr_i.rs1};
        end
        // or is it an immediate (including PC), this is not the case for a store and control flow instructions
        if (issue_instr_i.use_imm && (issue_instr_i.fu != STORE) && (issue_instr_i.fu != CTRL_FLOW)) begin
            operand_b_n = issue_instr_i.result;
        end
    end
    // FU select, assert the correct valid out signal (in the next cycle)
    always_comb begin : unit_valid
        alu_valid_n    = 1'b0;
        lsu_valid_n    = 1'b0;
        mult_valid_n   = 1'b0;
        csr_valid_n    = 1'b0;
        branch_valid_n = 1'b0;
        // Exception pass through:
        // If an exception has occurred simply pass it through
        // we do not want to issue this instruction
        if (~issue_instr_i.ex.valid && issue_instr_valid_i && issue_ack_o) begin
            case (issue_instr_i.fu)
                ALU:
                    alu_valid_n    = 1'b1;
                CTRL_FLOW:
                    branch_valid_n = 1'b1;
                MULT:
                    mult_valid_n   = 1'b1;
                LOAD, STORE:
                    lsu_valid_n    = 1'b1;
                CSR:
                    csr_valid_n    = 1'b1;
                default:;
            endcase
        end
        // if we got a flush request, de-assert the valid flag, otherwise we will start this
        // functional unit with the wrong inputs
        if (flush_i) begin
            alu_valid_n    = 1'b0;
            lsu_valid_n    = 1'b0;
            mult_valid_n   = 1'b0;
            csr_valid_n    = 1'b0;
            branch_valid_n = 1'b0;
        end
    end

    // --------------------
    // Debug Multiplexers
    // --------------------
    logic [4:0]  raddr_a, waddr;
    logic [63:0] wdata;
    logic        we;

    always_comb begin
        // get the address from the issue stage by default
        // read port
        debug_gpr_rdata_o = operand_a_regfile;
        raddr_a           = issue_instr_i.rs1[4:0];
        // write port
        waddr             = waddr_i[0];
        wdata             = wdata_i[0];
        we                = we_i[0];
        // we've got a debug request in
        if (debug_gpr_req_i) begin
            raddr_a = debug_gpr_addr_i;
            waddr   = debug_gpr_addr_i;
            wdata   = debug_gpr_wdata_i;
            we      = debug_gpr_we_i;
        end
    end

    // ----------------------
    // Integer Register File
    // ----------------------
    logic [1:0][63:0] rdata_o;

    assign operand_a_regfile = rdata_o[0];
    assign operand_b_regfile = rdata_o[1];

    ariane_regfile #(
        .DATA_WIDTH     ( 64 ),
        .NR_READ_PORTS  ( 2  ),
        .NR_WRITE_PORTS ( 2  ),
        .ZERO_REG_ZERO  ( 1  )
    ) i_ariane_regfile (
        .raddr_i   ( '{issue_instr_i.rs2[4:0], raddr_a} ),
        .rdata_o   ( rdata_o ),
        .waddr_i   ( '{waddr_i[1], waddr}               ),
        .wdata_i   ( '{wdata_i[1], wdata}               ),
        .we_i      ( '{we_i[1], we}                     ),
        .*
    );

    // ----------------------
    // Registers (ID <-> EX)
    // ----------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            operand_a_q           <= '{default: 0};
            operand_b_q           <= '{default: 0};
            imm_q                 <= 64'b0;
            alu_valid_q           <= 1'b0;
            branch_valid_q        <= 1'b0;
            mult_valid_q          <= 1'b0;
            lsu_valid_q           <= 1'b0;
            csr_valid_q           <= 1'b0;
            fu_q                  <= NONE;
            operator_q            <= ADD;
            trans_id_q            <= 5'b0;
            pc_o                  <= 64'b0;
            is_compressed_instr_o <= 1'b0;
            branch_predict_o      <= '{default: 0};
        end else begin
            operand_a_q           <= operand_a_n;
            operand_b_q           <= operand_b_n;
            imm_q                 <= imm_n;
            alu_valid_q           <= alu_valid_n;
            branch_valid_q        <= branch_valid_n;
            mult_valid_q          <= mult_valid_n;
            lsu_valid_q           <= lsu_valid_n;
            csr_valid_q           <= csr_valid_n;
            fu_q                  <= fu_n;
            operator_q            <= operator_n;
            trans_id_q            <= trans_id_n;
            pc_o                  <= issue_instr_i.pc;
            is_compressed_instr_o <= issue_instr_i.is_compressed;
            branch_predict_o      <= issue_instr_i.bp;
        end
    end

    `ifndef SYNTHESIS
    `ifndef verilator
     assert property (
        @(posedge clk_i) (branch_valid_q) |-> (!$isunknown(operand_a_q) && !$isunknown(operand_b_q)))
        else $warning ("Got unknown value in one of the operands");

    initial begin
        assert (NR_COMMIT_PORTS == 2) else $error("Only two commit ports are supported at the moment!");
    end
    `endif
    `endif
endmodule


