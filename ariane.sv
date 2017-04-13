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
        parameter N_EXT_PERF_COUNTERS = 0,
        parameter INSTR_RDATA_WIDTH   = 64
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
        input  logic [64:0]                    boot_addr_i,
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
    logic [31:0] instruction_i;
    logic instruction_valid_i;
    logic ready_o;
    alu_op operator_o;
    logic [63:0] operand_a_o;
    logic [63:0] operand_b_o;
    logic alu_ready_i;
    logic alu_valid_o;
    logic lsu_ready_i;
    logic lsu_valid_o;
    logic mult_ready_i;
    logic mult_valid_o;
    logic [4:0] waddr_a_i;
    logic [63:0] wdata_a_i;
    logic we_a_i;

    id_stage id_stage_i (
        .clk_i               ( clk_i               ),
        .rst_ni              ( rst_ni              ),
        .test_en_i           ( test_en_i           ),
        .flush_i             ( flush_i             ),
        .instruction_i       ( instruction_i       ),
        .instruction_valid_i ( instruction_valid_i ),
        .ready_o             ( ready_o             ),
        .operator_o          ( operator_o          ),
        .operand_a_o         ( operand_a_o         ),
        .operand_b_o         ( operand_b_o         ),
        .alu_ready_i         ( alu_ready_i         ),
        .alu_valid_o         ( alu_valid_o         ),
        .lsu_ready_i         ( lsu_ready_i         ),
        .lsu_valid_o         ( lsu_valid_o         ),
        .mult_ready_i        ( mult_ready_i        ),
        .mult_valid_o        ( mult_valid_o        ),
        .waddr_a_i           ( waddr_a_i           ),
        .wdata_a_i           ( wdata_a_i           ),
        .we_a_i              ( we_a_i              )
    );



    logic [63:0] alu_result;
    logic comparison_result_o;
    logic lsu_ready_o;
    logic lsu_valid_i;
    logic mult_ready_o;
    logic mult_valid_i;

ex_stage ex_stage_i (
    .clk_i               ( clk_i               ),
    .rst_ni              ( rst_ni              ),
    .operator_i          ( operator_o          ),
    .operand_a_i         ( operand_a_o         ),
    .operand_b_i         ( operand_b_o         ),
    .alu_result_o        ( alu_result          ),
    .comparison_result_o ( comparison_result_o ),
    .alu_ready_o         ( alu_ready_i         ),
    .alu_valid_i         ( alu_valid_o         ),
    .lsu_ready_o         ( lsu_ready_o         ),
    .lsu_valid_i         ( lsu_valid_i         ),
    .mult_ready_o        ( mult_ready_o        ),
    .mult_valid_i        ( mult_valid_i        )
);


endmodule // ariane