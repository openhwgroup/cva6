/* Ariane Top-level module
 * File:   scoreboard.sv
 * Author: Florian Zaruba <zarubaf@ethz.ch>
 * Date:   19.3.2017
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 */
import ariane_pkg::*;

module ariane
    #(
        parameter N_EXT_PERF_COUNTERS = 0
    )
    (
        input  logic                           clk_i,
        input  logic                           rst_n,
        input  logic                           clock_en_i,    // enable clock, otherwise it is gated
        input  logic                           test_en_i,     // enable all clock gates for testing

        // CPU Control Signals
        input  logic                           fetch_enable_i,
        output logic                           core_busy_o,
        input  logic [N_EXT_PERF_COUNTERS-1:0] ext_perf_counters_i,

        // Core ID, Cluster ID and boot address are considered more or less static
        input  logic [63:0]                    boot_addr_i,
        input  logic [ 3:0]                    core_id_i,
        input  logic [ 5:0]                    cluster_id_i,
        // Instruction memory interface
        mem_if.Slave                           instr_if,

        // Data memory interface
        mem_if.Slave                           data_if,

        // Interrupt inputs
        input  logic                           irq_i,                 // level sensitive IR lines
        input  logic [4:0]                     irq_id_i,
        output logic                           irq_ack_o,
        input  logic                           irq_sec_i,
        output logic                           sec_lvl_o,

        // Debug Interface
        debug_if.Slave                         debug_if
    );


    logic rst_ni;
    logic flush_i;
    // logic [31:0] instruction_i;
    // logic instruction_valid_i;
    logic ready_o;
    alu_op operator_o;
    logic [63:0] operand_a_o;
    logic [63:0] operand_b_o;
    logic alu_ready_i;
    logic alu_valid_i;
    logic lsu_ready_i;
    logic lsu_valid_o;
    logic mult_ready_i;
    logic mult_valid_o;
    logic [4:0] waddr_a_i;
    logic [63:0] wdata_a_i;
    logic we_a_i;
    logic [4:0] alu_trans_id, trans_id_o;
    logic alu_valid_o;
    logic [63:0] alu_result;
    // synth stuff
    assign flush_i = 1'b0;

    logic req_i;
    logic if_busy_o;
    logic id_ready_i;
    logic halt_if_i;
    logic instr_req_o;
    logic [63:0] instr_addr_o;
    logic instr_gnt_i;
    logic instr_rvalid_i;
    logic [31:0] instr_rdata_i;
    logic instr_valid_id_o;
    logic [31:0] instr_rdata_id_o;
    logic is_compressed_id_o;
    logic illegal_c_insn_id_o;
    logic [63:0] pc_if_o;
    logic [63:0] pc_id_o;
    logic comparison_result_o;
    logic lsu_ready_o;
    logic lsu_valid_i;
    logic mult_ready_o;
    logic mult_valid_i;
    priv_lvl_t priv_lvl_o;
    exception exception_o;

if_stage i_if_stage (
    .clk_i               ( clk_i                   ),
    .rst_ni              ( rst_ni                  ),
    .req_i               ( req_i                   ),
    .if_busy_o           ( if_busy_o               ),
    .id_ready_i          ( id_ready_i              ),
    .halt_if_i           ( halt_if_i               ),
    .instr_req_o         ( instr_if.data_req       ),
    .instr_addr_o        ( instr_if.address        ),
    .instr_gnt_i         ( instr_if.data_gnt       ),
    .instr_rvalid_i      ( instr_if.data_rvalid    ),
    .instr_rdata_i       ( instr_if.data_rdata     ),
    .instr_valid_id_o    ( instr_valid_id_o        ),
    .instr_rdata_id_o    ( instr_rdata_id_o        ),
    .is_compressed_id_o  ( is_compressed_id_o      ),
    .illegal_c_insn_id_o ( illegal_c_insn_id_o     ),
    .pc_if_o             ( pc_if_o                 ),
    .pc_id_o             ( pc_id_o                 ),
    .boot_addr_i         ( boot_addr_i             )
);

    id_stage
    #(
        .NR_WB_PORTS         ( 1                   )
    )
    id_stage_i (
        .clk_i               ( clk_i               ),
        .rst_ni              ( rst_ni              ),
        .test_en_i           ( test_en_i           ),
        .flush_i             ( flush_i             ),
        .instruction_i       ( instr_rdata_id_o    ),
        .instruction_valid_i ( instr_valid_id_o    ),
        .pc_if_i             ( pc_if_o             ), // PC from if
        .ex_i                (                     ), // exception from if
        .ready_o             ( ready_o             ),
        .operator_o          ( operator_o          ),
        .operand_a_o         ( operand_a_o         ),
        .operand_b_o         ( operand_b_o         ),
        .trans_id_o          ( trans_id_o          ),
        .alu_ready_i         ( alu_ready_i         ),
        .alu_valid_o         ( alu_valid_i         ),
        .lsu_ready_i         ( lsu_ready_i         ),
        .lsu_valid_o         ( lsu_valid_o         ),
        .mult_ready_i        ( mult_ready_i        ),
        .mult_valid_o        ( mult_valid_o        ),
        .trans_id_i          ( {alu_trans_id}      ),
        .wdata_i             ( {alu_result}        ),
        .wb_valid_i          ( {alu_valid_o}       ),

        .waddr_a_i           ( waddr_a_i           ),
        .wdata_a_i           ( wdata_a_i           ),
        .we_a_i              ( we_a_i              ),

        .commit_instr_o      ( commit_instr_o      ),
        .commit_ack_i        ( commit_ack_i        )
    );

    ex_stage ex_stage_i (
        .clk_i               ( clk_i               ),
        .rst_ni              ( rst_ni              ),
        .operator_i          ( operator_o          ),
        .operand_a_i         ( operand_a_o         ),
        .operand_b_i         ( operand_b_o         ),
        .trans_id_i          ( trans_id_o          ),
        .comparison_result_o ( comparison_result_o ),
        .alu_ready_o         ( alu_ready_i         ),
        .alu_valid_i         ( alu_valid_i         ),
        .alu_result_o        ( alu_result          ),
        .alu_trans_id_o      ( alu_trans_id        ),
        .alu_valid_o         ( alu_valid_o         ),

        .lsu_ready_o         ( lsu_ready_o         ),
        .lsu_valid_i         ( lsu_valid_i         ),

        .mult_ready_o        ( mult_ready_o        ),
        .mult_valid_i        ( mult_valid_i        )
    );

    commit_stage i_commit_stage (
        .clk_i           ( clk_i               ),
        .rst_ni          ( rst_ni              ),
        .priv_lvl_o      ( priv_lvl_o          ),
        .exception_o     ( exception_o         ),
        .commit_instr_i  ( commit_instr_o      ),
        .commit_ack_o    ( commit_ack_i        ),
        .waddr_a_o       ( waddr_a_i           ),
        .wdata_a_o       ( wdata_a_i           ),
        .we_a_o          ( we_a_i              )
    );

endmodule // ariane