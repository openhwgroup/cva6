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
        parameter N_EXT_PERF_COUNTERS          = 0
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


    logic flush_i;
    logic fetch_enable;
    // logic [31:0] instruction_i;
    // logic instruction_valid_i;
    logic ready_o;
    fu_op operator_o;
    logic [63:0] operand_a_o;
    logic [63:0] operand_b_o;
    logic alu_ready_i;
    logic alu_valid_i;
    logic lsu_valid_o;
    logic [4:0] waddr_a_i;
    logic [63:0] wdata_a_i;
    logic we_a_i;
    logic [TRANS_ID_BITS-1:0] alu_trans_id, lsu_trans_id, trans_id_o;
    logic alu_valid_o;
    logic [63:0] alu_result, lsu_result;
    // synth stuff
    assign flush_i = 1'b0;

    logic if_busy_o;
    logic id_ready_i;
    logic halt_if_i;
    logic [31:0] fetch_rdata_o;
    logic instr_valid_id_o;
    logic [31:0] instr_rdata_id_o;
    logic is_compressed_id_o;
    logic illegal_c_insn_id_o;
    logic [63:0] pc_if_o, imm_o;
    logic [63:0] pc_id_o;
    logic comparison_result_o;
    logic lsu_ready_o;
    logic lsu_valid_i;
    logic mult_ready_o;
    logic mult_valid_i;
    logic commit_ack_i;
    priv_lvl_t priv_lvl_o;
    exception exception_o;
    exception exception_if;
    scoreboard_entry commit_instr_o;

    logic enable_translation_i;
    logic fetch_req_i;
    logic fetch_gnt_o;
    logic fetch_valid_o;
    logic fetch_err_o;
    logic [63:0] fetch_vaddr_i;
    priv_lvl_t priv_lvl_i;
    logic flag_pum_i;
    logic flag_mxr_i;
    logic [37:0] pd_ppn_i;
    logic [0:0] asid_i;
    logic flush_tlb_i;

    assign id_ready_i = 1'b1;
    assign halt_if_i = 1'b0;

    if_stage i_if_stage (
        .clk_i               ( clk_i                   ),
        .rst_ni              ( rst_n                   ),
        .flush_i             ( 1'b0                    ),
        .req_i               ( fetch_enable            ),
        .if_busy_o           ( if_busy_o               ),
        .id_ready_i          ( id_ready_i              ),
        .halt_if_i           ( halt_if_i               ),
        .instr_req_o         ( fetch_req_i             ),
        .instr_addr_o        ( fetch_vaddr_i           ),
        .instr_gnt_i         ( fetch_gnt_o             ),
        .instr_rvalid_i      ( fetch_valid_o           ),
        .instr_rdata_i       ( fetch_rdata_o           ),
        .instr_valid_id_o    ( instr_valid_id_o        ),
        .instr_rdata_id_o    ( instr_rdata_id_o        ),
        .is_compressed_id_o  ( is_compressed_id_o      ),
        .illegal_c_insn_id_o ( illegal_c_insn_id_o     ),
        .pc_if_o             ( pc_if_o                 ),
        .pc_id_o             ( pc_id_o                 ),
        .ex_o                ( exception_if            ),
        .boot_addr_i         ( boot_addr_i             )
    );

    id_stage
    #(
        .NR_ENTRIES          ( NR_SB_ENTRIES                ),
        .NR_WB_PORTS         ( NR_WB_PORTS                  )
    )
    id_stage_i (
        .clk_i               ( clk_i                        ),
        .rst_ni              ( rst_n                        ),
        .test_en_i           ( test_en_i                    ),
        .flush_i             ( flush_i                      ),
        .instruction_i       ( instr_rdata_id_o             ),
        .instruction_valid_i ( instr_valid_id_o             ),
        .pc_if_i             ( pc_if_o                      ), // PC from if
        .ex_i                ( exception_if                 ), // exception from if
        .ready_o             ( ready_o                      ),
        .operator_o          ( operator_o                   ),
        .operand_a_o         ( operand_a_o                  ),
        .operand_b_o         ( operand_b_o                  ),
        .imm_o               ( imm_o                        ),
        .trans_id_o          ( trans_id_o                   ),
        .alu_ready_i         ( alu_ready_i                  ),
        .alu_valid_o         ( alu_valid_i                  ),
        .lsu_ready_i         (                              ),
        .lsu_valid_o         (                              ),
        .mult_ready_i        (                              ),
        .mult_valid_o        (                              ),
        .trans_id_i          ( {alu_trans_id, lsu_trans_id} ),
        .wdata_i             ( {alu_result,   lsu_result}   ),
        .wb_valid_i          ( {alu_valid_o, lsu_valid_o}   ),

        .waddr_a_i           ( waddr_a_i                    ),
        .wdata_a_i           ( wdata_a_i                    ),
        .we_a_i              ( we_a_i                       ),

        .commit_instr_o      ( commit_instr_o               ),
        .commit_ack_i        ( commit_ack_i                 )
    );

    ex_stage ex_stage_i (
        .clk_i               ( clk_i                 ),
        .rst_ni              ( rst_n                 ),
        .flush_i             ( 1'b0                  ),
        .operator_i          ( operator_o            ),
        .operand_a_i         ( operand_a_o           ),
        .operand_b_i         ( operand_b_o           ),
        .imm_i               ( imm_o                 ),
        .trans_id_i          ( trans_id_o            ),
        .comparison_result_o ( comparison_result_o   ),

        .alu_ready_o         ( alu_ready_i           ),
        .alu_valid_i         ( alu_valid_i           ),
        .alu_result_o        ( alu_result            ),
        .alu_trans_id_o      ( alu_trans_id          ),
        .alu_valid_o         ( alu_valid_o           ),

        .lsu_ready_o         ( lsu_ready_o           ),
        .lsu_valid_i         ( lsu_valid_i           ),
        .lsu_result_o        ( lsu_result            ),
        .lsu_trans_id_o      ( lsu_trans_id          ),
        .lsu_valid_o         ( lsu_valid_o           ),

        // memory management
        .enable_translation_i ( 1'b0                 ),  // from CSR
        .fetch_req_i          ( fetch_req_i          ),
        .fetch_gnt_o          ( fetch_gnt_o          ),
        .fetch_valid_o        ( fetch_valid_o        ),
        .fetch_err_o          ( fetch_err_o          ),
        .fetch_vaddr_i        ( fetch_vaddr_i        ),
        .fetch_rdata_o        ( fetch_rdata_o        ),
        .priv_lvl_i           ( priv_lvl_i           ),  // from CSR
        .flag_pum_i           ( flag_pum_i           ),  // from CSR
        .flag_mxr_i           ( flag_mxr_i           ),  // from CSR
        .pd_ppn_i             ( pd_ppn_i             ),  // from CSR
        .asid_i               ( asid_i               ),  // from CSR
        .flush_tlb_i          ( flush_tlb_i          ),
        .instr_if             ( instr_if             ),
        .data_if              ( data_if              ),

        .mult_ready_o        ( mult_ready_o          ),
        .mult_valid_i        ( mult_valid_i          )
    );

    commit_stage commit_stage_i (
        .clk_i               ( clk_i                 ),
        .rst_ni              ( rst_n                 ),
        .priv_lvl_o          ( priv_lvl_o            ),
        .exception_o         ( exception_o           ),
        .commit_instr_i      ( commit_instr_o        ),
        .commit_ack_o        ( commit_ack_i          ),
        .waddr_a_o           ( waddr_a_i             ),
        .wdata_a_o           ( wdata_a_i             ),
        .we_a_o              ( we_a_i                )
    );

    always_ff @(posedge clk_i or negedge rst_n) begin
        if(~rst_n) begin
            fetch_enable <= 0;
        end else begin
            fetch_enable <= fetch_enable_i;
        end
    end

endmodule // ariane