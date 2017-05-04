// Author: Florian Zaruba, ETH Zurich
// Date: 08.04.2017
// Description: Issues instruction from the scoreboard and fetches the operands
//              This also includes all the forwarding logic
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
import ariane_pkg::*;

module issue_read_operands (
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    input  logic                                   test_en_i,
    // flush
    input  logic                                   flush_i,
    // coming from scoreboard
    input  scoreboard_entry                        issue_instr_i,
    input  logic                                   issue_instr_valid_i,
    output logic                                   issue_ack_o,
    // lookup rd in scoreboard
    output logic [4:0]                             rs1_o,
    input  logic [63:0]                            rs1_i,
    input  logic                                   rs1_valid_i,
    output logic [4:0]                             rs2_o,
    input  logic [63:0]                            rs2_i,
    input  logic                                   rs2_valid_i,
    // get clobber input
    input  fu_t [31:0]                             rd_clobber_i,
    // To FU, just single issue for now
    output fu_op                                   operator_o,
    output logic [63:0]                            operand_a_o,
    output logic [63:0]                            operand_b_o,
    output logic [63:0]                            imm_o,           // output immediate for the LSU
    output logic [TRANS_ID_BITS-1:0]               trans_id_o,
    // ALU 1
    input  logic                                   alu_ready_i,      // FU is ready
    output logic                                   alu_valid_o,      // Output is valid
    // LSU
    input  logic                                   lsu_ready_i,      // FU is ready
    output logic                                   lsu_valid_o,      // Output is valid
    // MULT
    input  logic                                   mult_ready_i,      // FU is ready
    output logic                                   mult_valid_o,      // Output is valid
    // commit port
    input  logic [4:0]                             waddr_a_i,
    input  logic [63:0]                            wdata_a_i,
    input  logic                                   we_a_i
);
    logic stall; // stall signal, we do not want to fetch any more entries
    logic fu_busy; // functional unit is busy
    logic [63:0] operand_a_regfile, operand_b_regfile;  // operands coming from regfile

    // output flipflop (ID <-> EX)
    logic [63:0] operand_a_n, operand_a_q, operand_b_n, operand_b_q, imm_n, imm_q;
    logic alu_valid_n, alu_valid_q;
    logic [TRANS_ID_BITS-1:0] trans_id_n, trans_id_q;
    fu_op operator_n, operator_q;

    // forwarding signals
    logic forward_rs1, forward_rs2;

    assign operand_a_o = operand_a_q;
    assign operand_b_o = operand_b_q;
    assign operator_o  = operator_q;
    assign alu_valid_o = alu_valid_q;
    assign trans_id_o  = trans_id_q;
    assign imm_o       = imm_q;
    // ---------------
    // Issue Stage
    // ---------------
    // We can issue an instruction if we do not detect that any other instruction is writing the same
    // destination register.
    // We also need to check if there is an unresolved branch in the scoreboard.
    always_comb begin : issue
        // default assignment
        issue_ack_o = 1'b0;
        // check that we didn't stall, that the instruction we got is valid
        // and that the functional unit we need is not busy
        if (issue_instr_valid_i) begin
            if (~stall && ~fu_busy) begin
                // check that the corresponding functional unit is not busy
                // no other instruction has the same destination register -> fetch the instruction
                if (rd_clobber_i[issue_instr_i.rd] == NONE) begin
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
    always_comb begin : unit_busy
        unique case (issue_instr_i.fu)
            NONE:
                fu_busy = 1'b0;
            ALU:
                fu_busy = ~alu_ready_i;
            MULT:
                fu_busy = ~mult_ready_i;
            LSU:
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
        // poll the scoreboard for those values
        rs1_o = issue_instr_i.rs1;
        rs2_o = issue_instr_i.rs2;
        // 1. check if the source registers are clobberd
        // 2. poll the scoreboard
        if (rd_clobber_i[issue_instr_i.rs1] != NONE) begin
            // the operand is available, forward it
            if (rs1_valid_i)
                forward_rs1 = 1'b1;
            else // the operand is not available -> stall
                stall = 1'b1;

        end

        if (rd_clobber_i[issue_instr_i.rs2] != NONE) begin
            // the operand is available, forward it
            if (rs2_valid_i)
                forward_rs2 = 1'b1;
            else // the operand is not available -> stall
                stall = 1'b1;
        end


    end
    // Forwarding/Output MUX
    always_comb begin : forwarding
        // default is regfile
        operand_a_n = operand_a_regfile;
        operand_b_n = operand_b_regfile;

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

        // or is it an immediate (including PC), this is not the case for a store
        if (issue_instr_i.use_imm && issue_instr_i.op != SD
                                  && issue_instr_i.op != SW
                                  && issue_instr_i.op != SH
                                  && issue_instr_i.op != SB
                                  && issue_instr_i.op != SBU ) begin
            operand_b_n = issue_instr_i.result;
        end
        // immediates are the third operands in the store case
        imm_n      = issue_instr_i.result;
        trans_id_n = issue_instr_i.trans_id;
        operator_n = issue_instr_i.op;
    end
    // FU select
    always_comb begin : unit_valid
        alu_valid_n  = 1'b0;
        lsu_valid_o  = 1'b0;
        mult_valid_o = 1'b0;
        // Exception pass through
        // if an exception has occurred simply pass it through
        if (~issue_instr_i.ex.valid && issue_instr_valid_i) begin
            case (issue_instr_i.fu)
                ALU:
                    alu_valid_n  = 1'b1;
                MULT:
                    mult_valid_o = 1'b1;
                LSU:
                    lsu_valid_o  = 1'b1;
                default: begin

                end
            endcase
        end
    end

    regfile #(
        .DATA_WIDTH     ( 64                  )
    )
    regfile_i (
        // Clock and Reset
        .clk            ( clk_i               ),
        .rst_n          ( rst_ni              ),
        .test_en_i      ( test_en_i           ),

        .raddr_a_i      ( issue_instr_i.rs1   ),
        .rdata_a_o      ( operand_a_regfile   ),

        .raddr_b_i      ( issue_instr_i.rs2   ),
        .rdata_b_o      ( operand_b_regfile   ),

        .waddr_a_i      ( waddr_a_i           ),
        .wdata_a_i      ( wdata_a_i           ),
        .we_a_i         ( we_a_i              )
    );

    // Registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            operand_a_q          <= '{default: 0};
            operand_b_q          <= '{default: 0};
            alu_valid_q          <= 1'b0;
            operator_q           <= ADD;
            trans_id_q           <= 5'b0;
        end else begin
            operand_a_q          <= operand_a_n;
            operand_b_q          <= operand_b_n;
            alu_valid_q          <= alu_valid_n;
            operator_q           <= operator_n;
            trans_id_q           <= trans_id_n;
        end
    end
endmodule


