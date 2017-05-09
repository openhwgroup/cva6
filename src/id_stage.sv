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

module id_stage #(
    parameter int  NR_ENTRIES = 4,
    parameter int  NR_WB_PORTS = 4
    )(
    input  logic                                     clk_i,     // Clock
    input  logic                                     rst_ni,    // Asynchronous reset active low
    input  logic                                     test_en_i, // Test Enable

    input  logic                                     flush_i,
    // from IF
    input  logic [31:0]                              instruction_i,
    input  logic                                     instruction_valid_i,
    input  logic                                     is_compressed_i,
    input  logic [63:0]                              pc_if_i,
    input  exception                                 ex_if_i,       // we already got an exception in IF

    output logic                                     ready_o,    // id is ready
    output fu_op                                     operator_o,
    output logic [63:0]                              operand_a_o,
    output logic [63:0]                              operand_b_o,
    output logic [63:0]                              operand_c_o,
    output logic [63:0]                              imm_o,
    output logic [TRANS_ID_BITS-1:0]                 trans_id_o,

    input  logic                                     alu_ready_i,
    output logic                                     alu_valid_o,

    output logic                                     branch_valid_o,
    output logic [63:0]                              predict_address_o,
    output logic                                     predict_taken_o,

    input  logic                                     lsu_ready_i,
    output logic                                     lsu_valid_o,

    input  logic                                     mult_ready_i,
    output logic                                     mult_valid_o,

    input  logic                                     csr_ready_i,
    output logic                                     csr_valid_o,

    // write back port
    input logic [NR_WB_PORTS-1:0][TRANS_ID_BITS-1:0] trans_id_i,
    input logic [NR_WB_PORTS-1:0][63:0]              wdata_i,
    input exception [NR_WB_PORTS-1:0]                ex_ex_i, // exception from execute stage
    input logic [NR_WB_PORTS-1:0]                    wb_valid_i,
    // commit port
    input  logic[4:0]                                waddr_a_i,
    input  logic[63:0]                               wdata_a_i,
    input  logic                                     we_a_i,

    output scoreboard_entry                          commit_instr_o,
    input  logic                                     commit_ack_i
);

    // Global signals
    logic full;
    // ---------------------------------------------------
    // Scoreboard (SB) <-> Issue and Read Operands (iro)
    // ---------------------------------------------------
    fu_t  [31:0]     rd_clobber_sb_iro;
    logic [4:0]      rs1_iro_sb;
    logic [63:0]     rs1_sb_iro;
    logic            rs1_valid_sb_iro;
    logic [4:0]      rs2_iro_sb;
    logic [63:0]     rs2_sb_iro;
    logic            rs2_valid_iro_sb;
    scoreboard_entry issue_instr_sb_iro;
    logic            issue_instr_valid_sb_iro;
    logic            issue_ack_iro_sb;
    // ---------------------------------------------------
    // Decoder (DC) <-> Scoreboard (SB)
    // ---------------------------------------------------
    scoreboard_entry decoded_instr_dc_sb;

    // TODO: Branching logic
    assign ready_o = ~full;

    decoder decoder_i (
        .clk_i                   ( clk_i                    ),
        .rst_ni                  ( rst_ni                   ),
        .pc_i                    ( pc_if_i                  ),
        .is_compressed_i         ( is_compressed_i          ),
        .instruction_i           ( instruction_i            ),
        .ex_i                    ( ex_if_i                  ),
        .instruction_o           ( decoded_instr_dc_sb      ),
        .is_control_flow_instr_o (                          )
    );

    scoreboard  #(
        .NR_ENTRIES            ( NR_ENTRIES               ),
        .NR_WB_PORTS           ( NR_WB_PORTS              )
    )
    scoreboard_i
    (
        .full_o                ( full                     ),
        .flush_i               ( flush_i                  ),
        .rd_clobber_o          ( rd_clobber_sb_iro        ),
        .rs1_i                 ( rs1_iro_sb               ),
        .rs1_o                 ( rs1_sb_iro               ),
        .rs1_valid_o           ( rs1_valid_sb_iro         ),
        .rs2_i                 ( rs2_iro_sb               ),
        .rs2_o                 ( rs2_sb_iro               ),
        .rs2_valid_o           ( rs2_valid_iro_sb         ),
        .commit_instr_o        ( commit_instr_o           ),
        .commit_ack_i          ( commit_ack_i             ),
        .decoded_instr_i       ( decoded_instr_dc_sb      ),
        .decoded_instr_valid_i ( instruction_valid_i      ),
        .issue_instr_o         ( issue_instr_sb_iro       ),
        .issue_instr_valid_o   ( issue_instr_valid_sb_iro ),
        .issue_ack_i           ( issue_ack_iro_sb         ),
        .trans_id_i            ( trans_id_i               ),
        .wdata_i               ( wdata_i                  ),
        .ex_i                  ( ex_ex_i                  ),
        .*
    );


    issue_read_operands issue_read_operands_i  (
        .issue_instr_i       ( issue_instr_sb_iro         ),
        .issue_instr_valid_i ( issue_instr_valid_sb_iro   ),
        .issue_ack_o         ( issue_ack_iro_sb           ),
        .rs1_o               ( rs1_iro_sb                 ),
        .rs1_i               ( rs1_sb_iro                 ),
        .rs1_valid_i         ( rs1_valid_sb_iro           ),
        .rs2_o               ( rs2_iro_sb                 ),
        .rs2_i               ( rs2_sb_iro                 ),
        .rs2_valid_i         ( rs2_valid_iro_sb           ),
        .rd_clobber_i        ( rd_clobber_sb_iro          ),
        .*
    );

endmodule