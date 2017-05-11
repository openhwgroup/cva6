// Author: Florian Zaruba, ETH Zurich
// Date: 19.03.2017
// Description: Ariane Top-level module
//
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

module ariane
    #(
        parameter N_EXT_PERF_COUNTERS          = 0
    )
    (
        input  logic                           clk_i,
        input  logic                           rst_ni,
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
        output logic [63:0]                    instr_if_address_o,
        output logic                           instr_if_data_req_o,
        output logic [3:0]                     instr_if_data_be_o,
        input  logic                           instr_if_data_gnt_i,
        input  logic                           instr_if_data_rvalid_i,
        input  logic [31:0]                    instr_if_data_rdata_i,
        // Data memory interface
        output logic [63:0]                    data_if_address_o,
        output logic [63:0]                    data_if_data_wdata_o,
        output logic                           data_if_data_req_o,
        output logic                           data_if_data_we_o,
        output logic [7:0]                     data_if_data_be_o,
        input  logic                           data_if_data_gnt_i,
        input  logic                           data_if_data_rvalid_i,
        input  logic [63:0]                    data_if_data_rdata_i,
        // Interrupt inputs
        input  logic                           irq_i,                 // level sensitive IR lines
        input  logic [4:0]                     irq_id_i,
        output logic                           irq_ack_o,
        input  logic                           irq_sec_i,
        output logic                           sec_lvl_o,

        // Debug Interface
        input  logic                           debug_req_i,
        output logic                           debug_gnt_o,
        output logic                           debug_rvalid_o,
        input  logic [14:0]                    debug_addr_i,
        input  logic                           debug_we_i,
        input  logic [63:0]                    debug_wdata_i,
        output logic [63:0]                    debug_rdata_o,
        output logic                           debug_halted_o,
        input  logic                           debug_halt_i,
        input  logic                           debug_resume_i
    );

    // ------------------------------------------
    // Global Signals
    // Signals connecting more than one module
    // ------------------------------------------
    priv_lvl_t                priv_lvl;
    logic                     flush;
    logic                     fetch_enable;
    logic                     halt_if;
    logic [63:0]              pc_if;
    exception                 ex_commit; // exception from commit stage
    branchpredict             branchpredict;
    // --------------
    // PCGEN <-> IF
    // --------------
    logic [63:0]              pc_pcgen_if;
    logic                     set_pc_pcgen_if;
    logic                     is_branch_pcgen_if;
    // --------------
    // PCGEN <-> EX
    // --------------
    // --------------
    // PCGEN <-> CSR
    // --------------
    logic [63:0]              trap_vector_base_commit_pcgen;
    logic [63:0]              epc_commit_pcgen;
    // --------------
    // IF <-> ID
    // --------------
    logic                     busy_if_id;
    logic                     ready_id_if;
    logic [31:0]              fetch_rdata_id_if;
    logic                     instr_valid_if_id;
    logic [31:0]              instr_rdata_if_id;
    logic                     illegal_c_insn_if_id;
    logic                     is_compressed_if_id;
    logic                     illegal_c_insn_id_if;
    logic [63:0]              pc_id_if_id;
    exception                 exception_if_id;
    logic                     branch_valid_if_id;
    logic [63:0]              predict_address_if_id;
    logic                     predict_taken_if_id;
    // --------------
    // ID <-> EX
    // --------------
    logic [63:0]              imm_id_ex;
    logic                     ready_id_ex;
    logic [TRANS_ID_BITS-1:0] trans_id_id_ex;
    fu_op                     operator_id_ex;
    logic [63:0]              operand_a_id_ex;
    logic [63:0]              operand_b_id_ex;
    logic [63:0]              operand_c_id_ex;
    logic [63:0]              pc_id_ex;
    // ALU
    logic                     alu_ready_ex_id;
    logic                     alu_valid_id_ex;
    logic [TRANS_ID_BITS-1:0] alu_trans_id_ex_id;
    logic                     alu_valid_ex_id;
    logic [63:0]              alu_result_ex_id;
    exception                 alu_exception_ex_id;
    // Branches and Jumps
    logic                     branch_valid_id_ex;
    logic                     predict_branch_valid_id_ex;
    logic [63:0]              predict_address_id_ex;
    logic                     predict_taken_id_ex;
    // LSU
    logic [TRANS_ID_BITS-1:0] lsu_trans_id_ex_id;
    logic                     lsu_valid_id_ex;
    logic [63:0]              lsu_result_ex_id;
    logic                     lsu_ready_ex_id;
    logic                     lsu_valid_ex_id;
    exception                 lsu_exception_ex_id;
    // MULT
    logic                     mult_ready_ex_id;
    logic                     mult_valid_id_ex;
    // CSR
    logic                     csr_ready_ex_id;
    logic                     csr_valid_id_ex;
    logic [TRANS_ID_BITS-1:0] csr_trans_id_ex_id;
    logic [63:0]              csr_result_ex_id;
    logic                     csr_valid_ex_id;
    // --------------
    // EX <-> COMMIT
    // --------------
    // LSU Commit
    logic                     csr_commit_commit_ex;
    logic                     lsu_commit_commit_ex;
    // CSR Commit
    // --------------
    // ID <-> COMMIT
    // --------------
    scoreboard_entry          commit_instr_id_commit;
    logic                     commit_ack_commit_id;
    // --------------
    // COMMIT <-> ID
    // --------------
    logic [4:0]               waddr_a_commit_id;
    logic [63:0]              wdata_a_commit_id;
    logic                     we_a_commit_id;
    // --------------
    // IF <-> EX
    // --------------
    logic                     fetch_req_if_ex;
    logic                     fetch_gnt_ex_if;
    logic                     fetch_valid_ex_if;
    logic [31:0]              fetch_rdata_ex_if;
    logic                     fetch_err_ex_if;
    logic [63:0]              fetch_vaddr_if_ex;
    // --------------
    // EX <-> CSR
    // --------------
    logic                     enable_translation_csr_ex;
    logic                     flag_pum_csr_ex;
    logic                     flag_mxr_csr_ex;
    logic [37:0]              pd_ppn_csr_ex;
    logic [0:0]               asid_csr_ex;
    logic                     flush_tlb_csr_ex;
    logic [11:0]              csr_addr_ex_csr;
    // --------------
    // COMMIT <-> CSR
    // --------------
    fu_op                     csr_op_commit_csr;
    logic [63:0]              csr_wdata_commit_csr;
    logic [63:0]              csr_rdata_csr_commit;
    logic [63:0]              pc_commit_csr;
    logic [4:0]               irq_enable_csr_commit;
    exception                 csr_exception_csr_commit;
    // --------------
    // EX <-> CSR
    // --------------

    // * -> CTRL
    logic                     flush_csr_ctrl;
    logic                     flush_unissued_instr_ctrl_id;
    logic                     flush_scoreboard_ctrl_id;
    logic                     flush_ctrl_if;

    // TODO: Preliminary signal assignments
    logic flush_tlb;
    assign flush_tlb = 1'b0;
    assign flush = 1'b0;

    assign halt_if = 1'b0;
    // --------------
    // NPC Generation
    // --------------
    pcgen pcgen_i (
        .flush_i            ( flush                          ),
        .pc_if_i            ( pc_if                          ),
        .branchpredict_i    ( branchpredict                  ),
        .pc_if_o            ( pc_pcgen_if                    ),
        .set_pc_o           ( set_pc_pcgen_if                ),
        .is_branch_o        ( is_branch_pcgen_if             ),
        .boot_addr_i        ( boot_addr_i                    ),
        .epc_i              ( epc_commit_pcgen               ),
        .trap_vector_base_i ( trap_vector_base_commit_pcgen  ),
        .ex_i               ( ex_commit                      ),
        .*
    );
    // ---------
    // IF
    // ---------
    if_stage if_stage_i (
        .flush_i             ( flush_ctrl_if            ),
        .req_i               ( fetch_enable             ),
        .if_busy_o           (                          ), // ?
        .id_ready_i          ( ready_id_if              ),
        .halt_if_i           ( halt_if                  ),
        .set_pc_i            ( set_pc_pcgen_if          ),
        .is_branch_i         ( is_branch_pcgen_if       ),
        .branch_valid_o      ( branch_valid_if_id       ),
        .predict_address_o   ( predict_address_if_id    ),
        .predict_taken_o     ( predict_taken_if_id      ),
        .fetch_addr_i        ( pc_pcgen_if              ),
        .instr_req_o         ( fetch_req_if_ex          ),
        .instr_addr_o        ( fetch_vaddr_if_ex        ),
        .instr_gnt_i         ( fetch_gnt_ex_if          ),
        .instr_rvalid_i      ( fetch_valid_ex_if        ),
        .instr_rdata_i       ( fetch_rdata_ex_if        ),

        .instr_valid_id_o    ( instr_valid_if_id        ),
        .instr_rdata_id_o    ( instr_rdata_if_id        ),
        .is_compressed_id_o  ( is_compressed_if_id      ),
        .illegal_c_insn_id_o ( illegal_c_insn_if_id     ),
        .pc_if_o             ( pc_if                    ),
        .pc_id_o             ( pc_id_if_id              ),
        .ex_o                ( exception_if_id          ),
        .*
    );
    // ---------
    // ID
    // ---------
    id_stage
    #(
        .NR_ENTRIES          ( NR_SB_ENTRIES                ),
        .NR_WB_PORTS         ( NR_WB_PORTS                  )
    )
    id_stage_i (
        .test_en_i              ( test_en_i                                ),
        .flush_i                ( flush                                    ),
        .flush_unissued_instr_i ( flush_unissued_instr_ctrl_id             ),
        .flush_scoreboard_i     ( flush_scoreboard_ctrl_id                 ),
        .instruction_i          ( instr_rdata_if_id                        ),
        .instruction_valid_i    ( instr_valid_if_id                        ),
        .is_compressed_i        ( is_compressed_if_id                      ),
        .pc_if_i                ( pc_id_if_id                              ), // PC from if
        .ex_if_i                ( exception_if_id                          ), // exception from if
        .ready_o                ( ready_id_if                              ),
        // Functional Units
        .operator_o             ( operator_id_ex                           ),
        .operand_a_o            ( operand_a_id_ex                          ),
        .operand_b_o            ( operand_b_id_ex                          ),
        .operand_c_o            ( operand_c_id_ex                          ),
        .imm_o                  ( imm_id_ex                                ),
        .trans_id_o             ( trans_id_id_ex                           ),
        .pc_o                   ( pc_id_ex                                 ),
        .is_compressed_instr_o  ( is_compressed_instr_id_ex                ),
        // ALU
        .alu_ready_i            ( alu_ready_ex_id                          ),
        .alu_valid_o            ( alu_valid_id_ex                          ),
        // Branches and Jumps
        .branch_valid_i         ( branch_valid_if_id                       ),
        .predict_address_i      ( predict_address_if_id                    ),
        .predict_taken_i        ( predict_taken_if_id                      ),
        .branch_valid_o         ( branch_valid_id_ex                       ),
        .predict_branch_valid_o ( predict_branch_valid_id_ex               ),
        .predict_address_o      ( predict_address_id_ex                    ),
        .predict_taken_o        ( predict_taken_id_ex                      ),
        .branchpredict_i        ( branchpredict                            ), // in order to resolve the branch
        // LSU
        .lsu_ready_i            ( lsu_ready_ex_id                          ),
        .lsu_valid_o            ( lsu_valid_id_ex                          ),
        // Multiplier
        .mult_ready_i           ( mult_ready_ex_id                         ),
        .mult_valid_o           ( mult_valid_id_ex                         ),
        // CSR
        .csr_ready_i            ( csr_ready_ex_id                          ),
        .csr_valid_o            ( csr_valid_id_ex                          ),

        .trans_id_i             ( {alu_trans_id_ex_id,  lsu_trans_id_ex_id,  csr_trans_id_ex_id       }),
        .wdata_i                ( {alu_result_ex_id,    lsu_result_ex_id,    csr_result_ex_id         }),
        .ex_ex_i                ( {alu_exception_ex_id, lsu_exception_ex_id, {$bits(exception){1'b0}} }),
        .wb_valid_i             ( {alu_valid_ex_id,     lsu_valid_ex_id,     csr_valid_ex_id          }),

        .waddr_a_i              ( waddr_a_commit_id                        ),
        .wdata_a_i              ( wdata_a_commit_id                        ),
        .we_a_i                 ( we_a_commit_id                           ),

        .commit_instr_o         ( commit_instr_id_commit                   ),
        .commit_ack_i           ( commit_ack_commit_id                     ),
        .*
    );
    // ---------
    // EX
    // ---------
    ex_stage ex_stage_i (
        .flush_i                ( flush                      ),
        .operator_i             ( operator_id_ex             ),
        .operand_a_i            ( operand_a_id_ex            ),
        .operand_b_i            ( operand_b_id_ex            ),
        .operand_c_i            ( operand_c_id_ex            ),
        .imm_i                  ( imm_id_ex                  ),
        .trans_id_i             ( trans_id_id_ex             ),
        .pc_i                   ( pc_id_ex                   ),
        .is_compressed_instr_i  ( is_compressed_instr_id_ex  ),
        // ALU
        .alu_ready_o            ( alu_ready_ex_id            ),
        .alu_valid_i            ( alu_valid_id_ex            ),
        .alu_result_o           ( alu_result_ex_id           ),
        .alu_trans_id_o         ( alu_trans_id_ex_id         ),
        .alu_valid_o            ( alu_valid_ex_id            ),
        .alu_exception_o        ( alu_exception_ex_id        ),
        // Branches and Jumps
        .branch_valid_i         ( branch_valid_id_ex         ),
        .predict_branch_valid_i ( predict_branch_valid_id_ex ),
        .predict_address_i      ( predict_address_id_ex      ),
        .predict_taken_i        ( predict_taken_id_ex        ),
        .branchpredict_o        ( branchpredict              ),
        // LSU
        .lsu_ready_o            ( lsu_ready_ex_id            ),
        .lsu_valid_i            ( lsu_valid_id_ex            ),
        .lsu_result_o           ( lsu_result_ex_id           ),
        .lsu_trans_id_o         ( lsu_trans_id_ex_id         ),
        .lsu_valid_o            ( lsu_valid_ex_id            ),
        .lsu_commit_i           ( lsu_commit_commit_ex       ), // from commit
        .lsu_exception_o        ( lsu_exception_ex_id        ),
        // CSR
        .csr_ready_o            ( csr_ready_ex_id            ),
        .csr_valid_i            ( csr_valid_id_ex            ),
        .csr_trans_id_o         ( csr_trans_id_ex_id         ),
        .csr_result_o           ( csr_result_ex_id           ),
        .csr_valid_o            ( csr_valid_ex_id            ),
        .csr_addr_o             ( csr_addr_ex_csr            ),
        .csr_commit_i           ( csr_commit_commit_ex       ), // from commit
        // memory management
        .enable_translation_i   ( enable_translation_csr_ex  ), // from CSR
        .fetch_req_i            ( fetch_req_if_ex            ),
        .fetch_gnt_o            ( fetch_gnt_ex_if            ),
        .fetch_valid_o          ( fetch_valid_ex_if          ),
        .fetch_err_o            ( fetch_err_ex_if            ),
        .fetch_vaddr_i          ( fetch_vaddr_if_ex          ),
        .fetch_rdata_o          ( fetch_rdata_ex_if          ),
        .priv_lvl_i             ( priv_lvl                   ), // from CSR
        .flag_pum_i             ( flag_pum_csr_ex            ), // from CSR
        .flag_mxr_i             ( flag_mxr_csr_ex            ), // from CSR
        .pd_ppn_i               ( pd_ppn_csr_ex              ), // from CSR
        .asid_i                 ( asid_csr_ex                ), // from CSR
        .flush_tlb_i            ( flush_tlb                  ),

        .mult_ready_o           ( mult_ready_ex_id           ),
        .mult_valid_i           ( mult_valid_id_ex           ),
        .*
    );
    // ---------
    // Commit
    // ---------
    commit_stage commit_stage_i (
        .exception_o         ( ex_commit              ),
        .commit_instr_i      ( commit_instr_id_commit     ),
        .commit_ack_o        ( commit_ack_commit_id       ),
        .waddr_a_o           ( waddr_a_commit_id          ),
        .wdata_a_o           ( wdata_a_commit_id          ),
        .we_a_o              ( we_a_commit_id             ),
        .commit_lsu_o        ( lsu_commit_commit_ex       ),
        .commit_csr_o        ( csr_commit_commit_ex       ),
        .pc_o                ( pc_commit_csr              ),
        .csr_op_o            ( csr_op_commit_csr          ),
        .csr_wdata_o         ( csr_wdata_commit_csr       ),
        .csr_rdata_i         ( csr_rdata_csr_commit       ),
        .csr_exception_i     ( csr_exception_csr_commit   ),
        .irq_enable_i        ( irq_enable_csr_commit      ),
        .*
    );
    // ---------
    // CSR
    // ---------
    csr_regfile #(
        .ASID_WIDTH           ( ASID_WIDTH                      )
    )
    csr_regfile_i (
        .flush_o              ( flush_csr_ctrl                  ),
        .ex_i                 ( ex_commit                       ),
        .csr_op_i             ( csr_op_commit_csr               ),
        .csr_addr_i           ( csr_addr_ex_csr                 ),
        .csr_wdata_i          ( csr_wdata_commit_csr            ),
        .csr_rdata_o          ( csr_rdata_csr_commit            ),
        .pc_i                 ( pc_commit_csr                   ),
        .csr_exception_o      ( csr_exception_csr_commit        ),
        .irq_enable_o         (                                 ),
        .epc_o                ( epc_commit_pcgen                ),
        .trap_vector_base_o   ( trap_vector_base_commit_pcgen   ),
        .priv_lvl_o           ( priv_lvl                        ),

        .enable_translation_o ( enable_translation_csr_ex       ),
        .flag_pum_o           ( flag_pum_csr_ex                 ),
        .flag_mxr_o           ( flag_mxr_csr_ex                 ),
        .pd_ppn_o             ( pd_ppn_csr_ex                   ),
        .asid_o               ( asid_csr_ex                     ),
        .*
    );
    // ------------
    // Controller
    // ------------
    logic flush_commit_i;
    logic branchpredict_i;

    controller controller_i (
        .flush_bp_o             (                               ),
        .flush_scoreboard_o     ( flush_scoreboard_ctrl_id      ),
        .flush_unissued_instr_o ( flush_unissued_instr_ctrl_id  ),
        .flush_if_o             ( flush_ctrl_if                 ),
        .flush_id_o             (                               ),
        .flush_ex_o             (                               ),

        .flush_ready_lsu_i      (                               ),
        .flush_commit_i         ( flush_commit_i                ),
        .flush_csr_i            ( flush_csr_ctrl                ),
        .branchpredict_i        ( branchpredict                 ),
        .*
    );


    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            fetch_enable <= 0;
        end else begin
            fetch_enable <= fetch_enable_i;
        end
    end

endmodule // ariane