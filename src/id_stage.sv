// Author: Florian Zaruba, ETH Zurich
// Date: 15.04.2017
// Description: Description: Instruction decode, contains the logic for decode,
//              issue and read operands.
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

module id_stage (
    input  logic                                     clk_i,     // Clock
    input  logic                                     rst_ni,    // Asynchronous reset active low

    input  logic                                     flush_i,
    // from IF
    input  fetch_entry                               fetch_entry_i,
    input  logic                                     fetch_entry_valid_i,
    output logic                                     decoded_instr_ack_o, // acknowledge the instruction (fetch entry)

    // to ID
    output scoreboard_entry                          issue_entry_o,       // a decoded instruction
    output logic                                     issue_entry_valid_o, // issue entry is valid
    output logic                                     is_ctrl_flow_o,      // the instruction we issue is a ctrl flow instructions
    input  logic                                     issue_instr_ack_i,   // issue stage acknowledged sampling of instructions
    // from CSR file
    input  priv_lvl_t                                priv_lvl_i,          // current privilege level
    input  logic                                     tvm_i,
    input  logic                                     tw_i,
    input  logic                                     tsr_i
);
    // register stage
    struct packed {
        logic            valid;
        scoreboard_entry sbe;
        logic            is_ctrl_flow;

    } issue_n, issue_q;

    logic is_control_flow_instr;
    scoreboard_entry decoded_instruction;

    decoder decoder_i (
        .pc_i                    ( fetch_entry_i.address         ),
        .is_compressed_i         ( fetch_entry_i.is_compressed   ),
        .instruction_i           ( fetch_entry_i.instruction     ),
        .branch_predict_i        ( fetch_entry_i.branch_predict  ),
        .is_illegal_i            ( fetch_entry_i.is_illegal      ),
        .ex_i                    ( fetch_entry_i.ex              ),
        .instruction_o           ( decoded_instruction           ),
        .is_control_flow_instr_o ( is_control_flow_instr         ),
        .*
    );

    // ------------------
    // Output Registers
    // ------------------
    assign issue_entry_o = issue_q.sbe;
    assign issue_entry_valid_o = issue_q.valid;
    assign is_ctrl_flow_o = issue_q.is_ctrl_flow;

    always_comb begin
        issue_n             = issue_q;
        decoded_instr_ack_o = 1'b0;

        // if we have a space in the register and the fetch is valid, go get it
        if (!issue_q.valid && fetch_entry_valid_i) begin
            decoded_instr_ack_o = 1'b1;
            issue_n = { 1'b1, decoded_instruction, is_control_flow_instr};
            issue_n.valid = 1'b1;
        end

        // we have something in the register but issue stage already acknowledged
        if (issue_q.valid && issue_instr_ack_i) begin
            decoded_instr_ack_o = 1'b1;
            issue_n = { 1'b1, decoded_instruction, is_control_flow_instr};
        end

        // invalidate on a flush
        if (flush_i)
            issue_n.valid = 1'b0;
    end
    // -------------------------
    // Registers (ID <-> Issue)
    // -------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            issue_q <= '0;
        end else begin
            issue_q <= issue_n;
        end
    end

endmodule