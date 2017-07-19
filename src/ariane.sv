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
`ifndef verilator
`ifndef SYNTHESIS
import instruction_tracer_pkg::*;
`timescale 1ns / 1ps
`endif
`endif


module ariane
    #(
        parameter N_EXT_PERF_COUNTERS          = 0
    )
    (
        input  logic                           clk_i,
        input  logic                           rst_ni,
        input  logic                           clock_en_i,    // enable clock, otherwise it is gated
        input  logic                           test_en_i,     // enable all clock gates for testing

        output logic                           flush_icache_o, // request to flush icache
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
        input  logic [63:0]                    instr_if_data_rdata_i,
        // Data memory interface
        output logic [11:0]                    data_if_address_index_o,
        output logic [43:0]                    data_if_address_tag_o,
        output logic [63:0]                    data_if_data_wdata_o,
        output logic                           data_if_data_req_o,
        output logic                           data_if_data_we_o,
        output logic [7:0]                     data_if_data_be_o,
        output logic                           data_if_kill_req_o,
        output logic                           data_if_tag_valid_o,
        input  logic                           data_if_data_gnt_i,
        input  logic                           data_if_data_rvalid_i,
        input  logic [63:0]                    data_if_data_rdata_i,
        // Interrupt inputs
        input  logic [1:0]                     irq_i,                 // level sensitive IR lines
        input  logic [4:0]                     irq_id_i,
        output logic                           irq_ack_o,
        input  logic                           irq_sec_i,
        output logic                           sec_lvl_o,
        // Timer facilities
        input  logic [63:0]                    time_i,        // global time (most probably coming from an RTC)
        input  logic                           time_irq_i,    // timer interrupt in

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
    logic                     fetch_enable;
    exception                 ex_commit; // exception from commit stage
    branchpredict             resolved_branch;
    logic [63:0]              pc_commit;
    logic                     eret;
    logic                     commit_ack;

    // --------------
    // PCGEN <-> IF
    // --------------
    logic [63:0]              fetch_address_pcgen_if;
    branchpredict_sbe         branch_predict_pcgen_if;
    logic                     if_ready_if_pcgen;
    logic                     fetch_valid_pcgen_if;
    // --------------
    // PCGEN <-> COMMIT
    // --------------
    // --------------
    // PCGEN <-> CSR
    // --------------
    logic [63:0]              trap_vector_base_commit_pcgen;
    logic [63:0]              epc_commit_pcgen;
    // --------------
    // IF <-> ID
    // --------------
    fetch_entry               fetch_entry_if_id;
    logic                     ready_id_if;
    logic                     fetch_valid_if_id;
    logic                     decode_ack_id_if;
    exception                 exception_if_id;

    // --------------
    // ID <-> ISSUE
    // --------------
    scoreboard_entry          issue_entry_id_issue;
    logic                     issue_entry_valid_id_issue;
    logic                     is_ctrl_fow_id_issue;
    logic                     issue_instr_issue_id;

    // --------------
    // ISSUE <-> EX
    // --------------
    logic [63:0]              imm_id_ex;
    logic [TRANS_ID_BITS-1:0] trans_id_id_ex;
    fu_t                      fu_id_ex;
    fu_op                     operator_id_ex;
    logic [63:0]              operand_a_id_ex;
    logic [63:0]              operand_b_id_ex;
    logic [63:0]              pc_id_ex;
    logic                     is_compressed_instr_id_ex;
    // ALU
    logic                     alu_ready_ex_id;
    logic                     alu_valid_id_ex;
    logic [TRANS_ID_BITS-1:0] alu_trans_id_ex_id;
    logic                     alu_valid_ex_id;
    logic [63:0]              alu_result_ex_id;
    exception                 alu_exception_ex_id;
    // Branches and Jumps
    logic                     branch_ready_ex_id;
    logic [TRANS_ID_BITS-1:0] branch_trans_id_ex_id;
    logic [63:0]              branch_result_ex_id;
    exception                 branch_exception_ex_id;
    logic                     branch_valid_ex_id;
    logic                     branch_valid_id_ex;

    branchpredict_sbe         branch_predict_id_ex;
    logic                     resolve_branch_ex_id;
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
    // CSR Commit
    logic                     csr_commit_commit_ex;
    // LSU Commit
    logic                     lsu_commit_commit_ex;
    logic                     no_st_pending_ex_commit;
    // --------------
    // ID <-> COMMIT
    // --------------
    scoreboard_entry          commit_instr_id_commit;
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
    logic [63:0]              fetch_rdata_ex_if;
    exception                 fetch_ex_ex_if;
    logic [63:0]              fetch_vaddr_if_ex;
    // --------------
    // CSR <-> *
    // --------------
    logic                     enable_translation_csr_ex;
    logic                     en_ld_st_translation_csr_ex;
    priv_lvl_t                ld_st_priv_lvl_csr_ex;
    logic                     sum_csr_ex;
    logic                     mxr_csr_ex;
    logic [43:0]              satp_ppn_csr_ex;
    logic [0:0]               asid_csr_ex;
    logic [11:0]              csr_addr_ex_csr;
    fu_op                     csr_op_commit_csr;
    logic [63:0]              csr_wdata_commit_csr;
    logic [63:0]              csr_rdata_csr_commit;
    exception                 csr_exception_csr_commit;
    logic                     tvm_csr_id;
    logic                     tw_csr_id;
    logic                     tsr_csr_id;
    // --------------
    // CTRL <-> *
    // --------------
    logic                     flush_bp_ctrl_pcgen;
    logic                     flush_ctrl_pcgen;
    logic                     flush_csr_ctrl;
    logic                     flush_unissued_instr_ctrl_id;
    logic                     flush_ctrl_if;
    logic                     flush_ctrl_id;
    logic                     flush_ctrl_ex;
    logic                     flush_tlb_ctrl_ex;
    logic                     fence_i_commit_controller;
    logic                     sfence_vma_commit_controller;
    logic                     halt_ctrl_commit;
    logic                     halt_debug_ctrl;
    logic                     halt_csr_ctrl;

    assign sec_lvl_o = priv_lvl;
    // --------------
    // NPC Generation
    // --------------
    pcgen_stage pcgen_stage_i (
        .fetch_enable_i        ( fetch_enable                   ),
        .flush_i               ( flush_ctrl_pcgen               ),
        .flush_bp_i            ( flush_bp_ctrl_pcgen            ),
        .if_ready_i            ( ~if_ready_if_pcgen             ),
        .resolved_branch_i     ( resolved_branch                ),
        .fetch_address_o       ( fetch_address_pcgen_if         ),
        .fetch_valid_o         ( fetch_valid_pcgen_if           ),
        .branch_predict_o      ( branch_predict_pcgen_if        ),
        .boot_addr_i           ( boot_addr_i                    ),
        .pc_commit_i           ( pc_commit                      ),
        .epc_i                 ( epc_commit_pcgen               ),
        .eret_i                ( eret                           ),
        .trap_vector_base_i    ( trap_vector_base_commit_pcgen  ),
        .ex_valid_i            ( ex_commit.valid                ),
        .*
    );
    // ---------
    // IF
    // ---------
    if_stage if_stage_i (
        .flush_i               ( flush_ctrl_if                  ),
        .if_busy_o             ( if_ready_if_pcgen              ),
        .fetch_address_i       ( fetch_address_pcgen_if         ),
        .fetch_valid_i         ( fetch_valid_pcgen_if           ),
        .branch_predict_i      ( branch_predict_pcgen_if        ),
        .instr_req_o           ( fetch_req_if_ex                ),
        .instr_addr_o          ( fetch_vaddr_if_ex              ),
        .instr_gnt_i           ( fetch_gnt_ex_if                ),
        .instr_rvalid_i        ( fetch_valid_ex_if              ),
        .instr_rdata_i         ( fetch_rdata_ex_if              ),
        .instr_ex_i            ( fetch_ex_ex_if                 ), // fetch exception

        .fetch_entry_0_o       ( fetch_entry_if_id              ),
        .fetch_entry_valid_0_o ( fetch_valid_if_id              ),
        .fetch_ack_0_i         ( decode_ack_id_if               ),

        // Reserved for future use
        .fetch_entry_1_o       (                                ),
        .fetch_entry_valid_1_o (                                ),
        .fetch_ack_1_i         (                                ),
        .*
    );

    // ---------
    // ID
    // ---------
    id_stage id_stage_i (
        .flush_i                    ( flush_ctrl_if                   ),

        .fetch_entry_i              ( fetch_entry_if_id               ),
        .fetch_entry_valid_i        ( fetch_valid_if_id               ),
        .decoded_instr_ack_o        ( decode_ack_id_if                ),

        .issue_entry_o              ( issue_entry_id_issue            ),
        .issue_entry_valid_o        ( issue_entry_valid_id_issue      ),
        .is_ctrl_flow_o             ( is_ctrl_fow_id_issue            ),
        .issue_instr_ack_i          ( issue_instr_issue_id            ),

        .priv_lvl_i                 ( priv_lvl                        ),
        .tvm_i                      ( tvm_csr_id                      ),
        .tw_i                       ( tw_csr_id                       ),
        .tsr_i                      ( tsr_csr_id                      ),

        .*
    );

    // ---------
    // Issue
    // ---------
    issue_stage
    #(
        .NR_ENTRIES                 ( NR_SB_ENTRIES                   ),
        .NR_WB_PORTS                ( NR_WB_PORTS                     )
    )
    issue_stage_i (
        .flush_unissued_instr_i     ( flush_unissued_instr_ctrl_id             ),
        .flush_i                    ( flush_ctrl_id                            ),

        .decoded_instr_i            ( issue_entry_id_issue                     ),
        .decoded_instr_valid_i      ( issue_entry_valid_id_issue               ),
        .is_ctrl_flow_i             ( is_ctrl_fow_id_issue                     ),
        .decoded_instr_ack_o        ( issue_instr_issue_id                     ),

        // Functional Units
        .fu_o                       ( fu_id_ex                                 ),
        .operator_o                 ( operator_id_ex                           ),
        .operand_a_o                ( operand_a_id_ex                          ),
        .operand_b_o                ( operand_b_id_ex                          ),
        .imm_o                      ( imm_id_ex                                ),
        .trans_id_o                 ( trans_id_id_ex                           ),
        .pc_o                       ( pc_id_ex                                 ),
        .is_compressed_instr_o      ( is_compressed_instr_id_ex                ),
        // ALU
        .alu_ready_i                ( alu_ready_ex_id                          ),
        .alu_valid_o                ( alu_valid_id_ex                          ),
        // Branches and Jumps
        .branch_ready_i             ( branch_ready_ex_id                       ),
        .branch_valid_o             ( branch_valid_id_ex                       ), // branch is valid
        .branch_predict_o           ( branch_predict_id_ex                     ), // branch predict to ex
        .resolve_branch_i           ( resolve_branch_ex_id                     ), // in order to resolve the branch
        // LSU
        .lsu_ready_i                ( lsu_ready_ex_id                          ),
        .lsu_valid_o                ( lsu_valid_id_ex                          ),
        // Multiplier
        .mult_ready_i               ( mult_ready_ex_id                         ),
        .mult_valid_o               ( mult_valid_id_ex                         ),
        // CSR
        .csr_ready_i                ( csr_ready_ex_id                          ),
        .csr_valid_o                ( csr_valid_id_ex                          ),

        .trans_id_i                 ( {alu_trans_id_ex_id,       lsu_trans_id_ex_id,  branch_trans_id_ex_id,    csr_trans_id_ex_id       }),
        .wdata_i                    ( {alu_result_ex_id,         lsu_result_ex_id,    branch_result_ex_id,      csr_result_ex_id         }),
        .ex_ex_i                    ( {{$bits(exception){1'b0}}, lsu_exception_ex_id, branch_exception_ex_id,   {$bits(exception){1'b0}} }),
        .wb_valid_i                 ( {alu_valid_ex_id,          lsu_valid_ex_id,     branch_valid_ex_id,       csr_valid_ex_id          }),

        .waddr_a_i                  ( waddr_a_commit_id                        ),
        .wdata_a_i                  ( wdata_a_commit_id                        ),
        .we_a_i                     ( we_a_commit_id                           ),

        .commit_instr_o             ( commit_instr_id_commit                   ),
        .commit_ack_i               ( commit_ack                               ),
        .*
    );

    // ---------
    // EX
    // ---------
    ex_stage ex_stage_i (
        .flush_i                ( flush_ctrl_ex               ),
        .fu_i                   ( fu_id_ex                    ),
        .operator_i             ( operator_id_ex              ),
        .operand_a_i            ( operand_a_id_ex             ),
        .operand_b_i            ( operand_b_id_ex             ),
        .imm_i                  ( imm_id_ex                   ),
        .trans_id_i             ( trans_id_id_ex              ),
        .pc_i                   ( pc_id_ex                    ),
        .is_compressed_instr_i  ( is_compressed_instr_id_ex   ),
        // ALU
        .alu_ready_o            ( alu_ready_ex_id             ),
        .alu_valid_i            ( alu_valid_id_ex             ),
        .alu_result_o           ( alu_result_ex_id            ),
        .alu_trans_id_o         ( alu_trans_id_ex_id          ),
        .alu_valid_o            ( alu_valid_ex_id             ),
        .alu_exception_o        (                             ),
        // Branches and Jumps
        .branch_ready_o         ( branch_ready_ex_id          ),
        .branch_valid_o         ( branch_valid_ex_id          ),
        .branch_valid_i         ( branch_valid_id_ex          ),
        .branch_trans_id_o      ( branch_trans_id_ex_id       ),
        .branch_result_o        ( branch_result_ex_id         ),
        .branch_exception_o     ( branch_exception_ex_id      ),
        .branch_predict_i       ( branch_predict_id_ex        ), // branch predict to ex
        .resolved_branch_o      ( resolved_branch             ),
        .resolve_branch_o       ( resolve_branch_ex_id        ),
        // LSU
        .lsu_ready_o            ( lsu_ready_ex_id             ),
        .lsu_valid_i            ( lsu_valid_id_ex             ),
        .lsu_result_o           ( lsu_result_ex_id            ),
        .lsu_trans_id_o         ( lsu_trans_id_ex_id          ),
        .lsu_valid_o            ( lsu_valid_ex_id             ),
        .lsu_commit_i           ( lsu_commit_commit_ex        ), // from commit
        .lsu_exception_o        ( lsu_exception_ex_id         ),
        .no_st_pending_o        ( no_st_pending_ex_commit     ),

        // CSR
        .csr_ready_o            ( csr_ready_ex_id             ),
        .csr_valid_i            ( csr_valid_id_ex             ),
        .csr_trans_id_o         ( csr_trans_id_ex_id          ),
        .csr_result_o           ( csr_result_ex_id            ),
        .csr_valid_o            ( csr_valid_ex_id             ),
        .csr_addr_o             ( csr_addr_ex_csr             ),
        .csr_commit_i           ( csr_commit_commit_ex        ), // from commit
        // Memory Management
        .enable_translation_i   ( enable_translation_csr_ex   ), // from CSR
        .en_ld_st_translation_i ( en_ld_st_translation_csr_ex ),
        .flush_tlb_i            ( flush_tlb_ctrl_ex           ),
        .fetch_req_i            ( fetch_req_if_ex             ),
        .fetch_gnt_o            ( fetch_gnt_ex_if             ),
        .fetch_valid_o          ( fetch_valid_ex_if           ),
        .fetch_vaddr_i          ( fetch_vaddr_if_ex           ),
        .fetch_rdata_o          ( fetch_rdata_ex_if           ),
        .fetch_ex_o             ( fetch_ex_ex_if              ), // fetch exception to IF
        .priv_lvl_i             ( priv_lvl                    ), // from CSR
        .ld_st_priv_lvl_i       ( ld_st_priv_lvl_csr_ex       ), // from CSR
        .sum_i                  ( sum_csr_ex                  ), // from CSR
        .mxr_i                  ( mxr_csr_ex                  ), // from CSR
        .satp_ppn_i             ( satp_ppn_csr_ex             ), // from CSR
        .asid_i                 ( asid_csr_ex                 ), // from CSR

        .mult_ready_o           ( mult_ready_ex_id            ),
        .mult_valid_i           ( mult_valid_id_ex            ),
        .*
    );

    // ---------
    // Commit
    // ---------
    commit_stage commit_stage_i (
        .halt_i                 ( halt_ctrl_commit              ),
        .exception_o            ( ex_commit                     ),
        .commit_instr_i         ( commit_instr_id_commit        ),
        .commit_ack_o           ( commit_ack                    ),
        .no_st_pending_i        ( no_st_pending_ex_commit       ),
        .waddr_a_o              ( waddr_a_commit_id             ),
        .wdata_a_o              ( wdata_a_commit_id             ),
        .we_a_o                 ( we_a_commit_id                ),
        .commit_lsu_o           ( lsu_commit_commit_ex          ),
        .commit_csr_o           ( csr_commit_commit_ex          ),
        .pc_o                   ( pc_commit                     ),
        .csr_op_o               ( csr_op_commit_csr             ),
        .csr_wdata_o            ( csr_wdata_commit_csr          ),
        .csr_rdata_i            ( csr_rdata_csr_commit          ),
        .csr_exception_i        ( csr_exception_csr_commit      ),
        .fence_i_o              ( fence_i_commit_controller     ),
        .sfence_vma_o           ( sfence_vma_commit_controller  ),
        .*
    );

    // ---------
    // CSR
    // ---------
    csr_regfile #(
        .ASID_WIDTH             ( ASID_WIDTH                    )
    )
    csr_regfile_i (
        .flush_o                ( flush_csr_ctrl                ),
        .halt_csr_o             ( halt_csr_ctrl                 ),
        .commit_ack_i           ( commit_ack                    ),
        .ex_i                   ( ex_commit                     ),
        .csr_op_i               ( csr_op_commit_csr             ),
        .csr_addr_i             ( csr_addr_ex_csr               ),
        .csr_wdata_i            ( csr_wdata_commit_csr          ),
        .csr_rdata_o            ( csr_rdata_csr_commit          ),
        .pc_i                   ( pc_commit                     ),
        .csr_exception_o        ( csr_exception_csr_commit      ),
        .epc_o                  ( epc_commit_pcgen              ),
        .eret_o                 ( eret                          ),
        .trap_vector_base_o     ( trap_vector_base_commit_pcgen ),
        .priv_lvl_o             ( priv_lvl                      ),
        .ld_st_priv_lvl_o       ( ld_st_priv_lvl_csr_ex         ),
        .en_translation_o       ( enable_translation_csr_ex     ),
        .en_ld_st_translation_o ( en_ld_st_translation_csr_ex   ),
        .sum_o                  ( sum_csr_ex                    ),
        .mxr_o                  ( mxr_csr_ex                    ),
        .satp_ppn_o             ( satp_ppn_csr_ex               ),
        .asid_o                 ( asid_csr_ex                   ),
        .tvm_o                  ( tvm_csr_id                    ),
        .tw_o                   ( tw_csr_id                     ),
        .tsr_o                  ( tsr_csr_id                    ),
        .*
    );

    // ------------
    // Controller
    // ------------
    controller controller_i (
        // flush ports
        .flush_bp_o             ( flush_bp_ctrl_pcgen           ),
        .flush_pcgen_o          ( flush_ctrl_pcgen              ),
        .flush_unissued_instr_o ( flush_unissued_instr_ctrl_id  ),
        .flush_if_o             ( flush_ctrl_if                 ),
        .flush_id_o             ( flush_ctrl_id                 ),
        .flush_ex_o             ( flush_ctrl_ex                 ),
        .flush_tlb_o            ( flush_tlb_ctrl_ex             ),

        .halt_csr_i             ( halt_csr_ctrl                 ),
        .halt_debug_i           ( 1'b0                          ),
        .halt_o                 ( halt_ctrl_commit              ),
        // control ports
        .eret_i                 ( eret                          ),
        .ex_valid_i             ( ex_commit.valid               ),
        .flush_csr_i            ( flush_csr_ctrl                ),
        .resolved_branch_i      ( resolved_branch               ),
        .fence_i_i              ( fence_i_commit_controller     ),
        .sfence_vma_i           ( sfence_vma_commit_controller  ),

        .*
    );

    // -------------------
    // Instruction Tracer
    // -------------------
    `ifndef SYNTHESIS
    `ifndef verilator
    instruction_tracer_if tracer_if (clk_i);
    // assign instruction tracer interface
    // control signals
    assign tracer_if.rstn              = rst_ni;
    assign tracer_if.flush_unissued    = flush_unissued_instr_ctrl_id;
    assign tracer_if.flush             = flush_ctrl_ex;
    // fetch
    assign tracer_if.instruction       = id_stage_i.compressed_decoder_i.instr_o;
    assign tracer_if.fetch_valid       = id_stage_i.instr_realigner_i.fetch_entry_valid_o;
    assign tracer_if.fetch_ack         = id_stage_i.instr_realigner_i.fetch_ack_i;
    // Issue
    assign tracer_if.issue_ack         = issue_stage_i.scoreboard_i.issue_ack_i;
    assign tracer_if.issue_sbe         = issue_stage_i.scoreboard_i.issue_instr_o;
    // write-back
    assign tracer_if.waddr             = waddr_a_commit_id;
    assign tracer_if.wdata             = wdata_a_commit_id;
    assign tracer_if.we                = we_a_commit_id;
    // commit
    assign tracer_if.commit_instr      = commit_instr_id_commit;
    assign tracer_if.commit_ack        = commit_ack;
    // address translation
    // stores
    assign tracer_if.st_valid          = ex_stage_i.lsu_i.store_unit_i.store_buffer_i.valid_i;
    assign tracer_if.st_paddr          = ex_stage_i.lsu_i.store_unit_i.store_buffer_i.paddr_i;
    // loads
    assign tracer_if.ld_valid          = ex_stage_i.lsu_i.load_unit_i.tag_valid_o;
    assign tracer_if.ld_kill           = ex_stage_i.lsu_i.load_unit_i.kill_req_o;
    assign tracer_if.ld_paddr          = ex_stage_i.lsu_i.load_unit_i.paddr_i;
    // exceptions
    assign tracer_if.exception         = commit_stage_i.exception_o;
    // assign current privilege level
    assign tracer_if.priv_lvl          = priv_lvl;

    program instr_tracer (instruction_tracer_if tracer_if);
        instruction_tracer it = new (tracer_if, 1'b0);

        initial begin
            #15ns;
            it.create_file(cluster_id_i, core_id_i);
            it.trace();
        end

        final begin
            it.close();
        end
    endprogram

    instr_tracer instr_tracer_i (tracer_if);
    `endif
    `endif

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            fetch_enable <= 0;
        end else begin
            fetch_enable <= fetch_enable_i;
        end
    end

endmodule // ariane
