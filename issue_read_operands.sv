/* File:   issue_read_operands.sv
 * Author: Florian Zaruba <zarubaf@ethz.ch>
 * Date:   8.4.2017
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * Description: Issues instruction from the scoreboard and fetches the operands
 *              This also includes all the forwarding logic
 */
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
    input  logic [31:0][$bits(fu_t)-1:0]           rd_clobber_i,
    // To FU, just single issue for now
    output alu_op                                  operator_o,
    output logic [63:0]                            operand_a_o,
    output logic [63:0]                            operand_b_o,
    // ALU 1
    input  logic                                   alu_ready_i,      // FU is ready
    output logic                                   alu_valid_o,      // Output is valid
    // LSU
    input  logic                                   lsu_ready_i,      // FU is ready
    output logic                                   lsu_valid_o,      // Output is valid
    // MULT
    input  logic                                   mult_ready_i,      // FU is ready
    output logic                                   mult_valid_o,      // Output is valid
    // Forward port

    // commit port
    input  logic [4:0]                             waddr_a_i,
    input  logic [63:0]                            wdata_a_i,
    input  logic                                   we_a_i
);
    logic stall; // stall signal, we do not want to fetch any more entries
    logic fu_busy; // functional unit is busy
    scoreboard_entry sbe_n, sbe_q; // instruction register (ID <-> EX)
    logic [63:0] operand_a_regfile_n, operand_a_regfile_q, operand_b_regfile_n, operand_b_regfile_q; // operands coming from regfile
    logic forward_rs1, forward_rs2;

    // ---------------
    // Issue Stage
    // ---------------
    // We can issue an instruction if we do not detect that any other instruction is writing the same
    // destination register.
    // We also need to check if there is an unresolved branch in the scoreboard.
    always_comb begin : issue
        // default assignment
        sbe_n = sbe_q;
        issue_ack_o = 1'b0;
        // check that we didn't stall, that the instruction we got is valid
        // and that the functional unit we need is not busy
        if (~stall && issue_instr_valid_i && ~fu_busy) begin
            // check that the corresponding functional unit is not busy
            // no other instruction has the same destination register -> fetch the instruction
            if (rd_clobber_i[issue_instr_i.rd] == NONE) begin
                sbe_n = issue_instr_i;
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
            CSR:
                fu_busy = 1'b0;
            default:
                fu_busy = 1'b0;
        endcase
    end

    // ---------------
    // Register stage
    // ---------------
    assign operator_o  = sbe_q.op;
    // check that all operands are available, otherwise stall
    // forward corresponding register
    always_comb begin : operands_available
        stall = 1'b0;
        // operand forwarding signals
        forward_rs1 = 1'b0;
        forward_rs2 = 1'b0;
        // address needs to be applied one cycle earlier
        rs1_o = issue_instr_i.rs1;
        rs2_o = issue_instr_i.rs2;
        // 1. check if the source registers are clobberd
        // 2. poll the scoreboard
        if (rd_clobber_i[sbe_q.rs1] != NONE) begin
            // the operand is available, forward it
            if (rs1_valid_i)
                forward_rs1 = 1'b1;
            else // the operand is not available -> stall
                stall = 1'b1;

        end

        if (rd_clobber_i[sbe_q.rs2] != NONE) begin
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
        operand_a_o = operand_a_regfile_q;
        operand_b_o = operand_b_regfile_q;

        // or should we forward
        if (forward_rs1) begin
            operand_a_o  = rs1_i;
        end

        if (forward_rs2) begin
            operand_b_o  = rs2_i;
        end

        // or is it an immediate (including PC)
        if (sbe_q.use_imm) begin
            operand_b_o = sbe_q.imm;
        end

    end
    // FU select
    always_comb begin : unit_valid
        alu_valid_o  = 1'b0;
        lsu_valid_o  = 1'b0;
        mult_valid_o = 1'b0;
        // Exception pass through
        // if an exception has occurred simply pass it through
        if (~sbe_q.ex.valid) begin
            case (sbe_q.fu)
                ALU:
                    alu_valid_o  = 1'b1;
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
        .rdata_a_o      ( operand_a_regfile_n ),

        .raddr_b_i      ( issue_instr_i.rs2   ),
        .rdata_b_o      ( operand_b_regfile_n ),

        .waddr_a_i      ( waddr_a_i           ),
        .wdata_a_i      ( wdata_a_i           ),
        .we_a_i         ( we_a_i              )
    );

    // Registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
           sbe_q                <= '{default: 0};
           operand_a_regfile_q  <= '{default: 0};
           operand_b_regfile_q  <= '{default: 0};
        end else begin
           sbe_q                <= sbe_n;
           operand_a_regfile_q  <= operand_a_regfile_n;
           operand_b_regfile_q  <= operand_b_regfile_n;
        end
    end
endmodule


