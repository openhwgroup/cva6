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
// Date: 19.03.2017
// Description: Ariane Top-level module

import ariane_pkg::*;
`ifndef verilator
`ifndef SYNTHESIS
import instruction_tracer_pkg::*;
`timescale 1ns / 1ps
`endif
`endif

module ariane #(
        parameter logic [63:0] CACHE_START_ADDR = 64'h4000_0000, // address on which to decide whether the request is cache-able or not
        parameter int unsigned AXI_ID_WIDTH     = 10,            // minimum 1
        parameter int unsigned AXI_USER_WIDTH   = 1              // minimum 1
    )(
        input  logic                           clk_i,
        input  logic                           rst_ni,
        input  logic                           test_en_i,              // enable all clock gates for testing

        input  logic                           flush_dcache_i,         // external request to flush data cache
        output logic                           flush_dcache_ack_o,     // finished data cache flush
        // CPU Control Signals
        input  logic                           fetch_enable_i,         // start fetching data
        // Core ID, Cluster ID and boot address are considered more or less static
        input  logic [63:0]                    boot_addr_i,            // reset boot address
        input  logic [ 3:0]                    core_id_i,              // core id in a multicore environment (reflected in a CSR)
        input  logic [ 5:0]                    cluster_id_i,           // PULP specific if core is used in a clustered environment
        // Instruction memory interface
        AXI_BUS.Master                         instr_if,
        // Data memory interface
        AXI_BUS.Master                         data_if,                // data cache refill port
        AXI_BUS.Master                         bypass_if,              // bypass axi port (disabled cache or uncacheable access)
        // Interrupt inputs
        input  logic [1:0]                     irq_i,                  // level sensitive IR lines, mip & sip
        input  logic                           ipi_i,                  // inter-processor interrupts
        output logic                           sec_lvl_o,              // current privilege level out
        // Timer facilities
        input  logic [63:0]                    time_i,                 // global time (most probably coming from an RTC)
        input  logic                           time_irq_i,             // timer interrupt in
        // Debug Interface
        input  logic                           debug_req_i,
        output logic                           debug_gnt_o,
        output logic                           debug_rvalid_o,
        input  logic [15:0]                    debug_addr_i,
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
    exception_t               ex_commit; // exception from commit stage
    branchpredict_t           resolved_branch;
    logic [63:0]              pc_commit;
    logic                     eret;
    logic [NR_COMMIT_PORTS-1:0] commit_ack;

    // --------------
    // PCGEN <-> IF
    // --------------
    logic [63:0]              fetch_address_pcgen_if;
    branchpredict_sbe_t       branch_predict_pcgen_if;
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
    fetch_entry_t             fetch_entry_if_id;
    logic                     ready_id_if;
    logic                     fetch_valid_if_id;
    logic                     decode_ack_id_if;
    exception_t               exception_if_id;

    // --------------
    // ID <-> ISSUE
    // --------------
    scoreboard_entry_t        issue_entry_id_issue;
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
    logic                     alu_branch_res_ex_id;
    exception_t               alu_exception_ex_id;
    // Branches and Jumps
    logic                     branch_ready_ex_id;
    logic [TRANS_ID_BITS-1:0] branch_trans_id_ex_id;
    logic [63:0]              branch_result_ex_id;
    exception_t               branch_exception_ex_id;
    logic                     branch_valid_ex_id;
    logic                     branch_valid_id_ex;

    branchpredict_sbe_t       branch_predict_id_ex;
    logic                     resolve_branch_ex_id;
    // LSU
    logic [TRANS_ID_BITS-1:0] lsu_trans_id_ex_id;
    logic                     lsu_valid_id_ex;
    logic [63:0]              lsu_result_ex_id;
    logic                     lsu_ready_ex_id;
    logic                     lsu_valid_ex_id;
    exception_t               lsu_exception_ex_id;
    // MULT
    logic                     mult_ready_ex_id;
    logic                     mult_valid_id_ex;
    logic [TRANS_ID_BITS-1:0] mult_trans_id_ex_id;
    logic [63:0]              mult_result_ex_id;
    logic                     mult_valid_ex_id;
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
    logic                     lsu_commit_ready_ex_commit;
    logic                     no_st_pending_ex_commit;
    // --------------
    // ID <-> COMMIT
    // --------------
    scoreboard_entry_t [NR_COMMIT_PORTS-1:0] commit_instr_id_commit;
    // --------------
    // COMMIT <-> ID
    // --------------
    logic [NR_COMMIT_PORTS-1:0][4:0]  waddr_commit_id;
    logic [NR_COMMIT_PORTS-1:0][63:0] wdata_commit_id;
    logic [NR_COMMIT_PORTS-1:0]       we_commit_id;
    // --------------
    // IF <-> EX
    // --------------
    logic                     fetch_req_if_ex;
    logic [63:0]              fetch_vaddr_if_ex;
    logic                     fetch_valid_ex_if;
    logic [63:0]              fetch_paddr_ex_if;
    exception_t               fetch_ex_ex_if;
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
    exception_t               csr_exception_csr_commit;
    logic                     tvm_csr_id;
    logic                     tw_csr_id;
    logic                     tsr_csr_id;
    logic                     dcache_en_csr_nbdcache;
    logic                     csr_write_fflags_commit_cs;
    // ----------------------------
    // Performance Counters <-> *
    // ----------------------------
    logic [11:0]              addr_csr_perf;
    logic [63:0]              data_csr_perf, data_perf_csr;
    logic                     we_csr_perf;

    logic                     itlb_miss_ex_perf;
    logic                     dtlb_miss_ex_perf;
    logic                     dcache_miss_ex_perf;
    // --------------
    // CTRL <-> *
    // --------------
    logic                     flush_bp_ctrl_pcgen;
    logic                     set_pc_ctrl_pcgen;
    logic                     flush_csr_ctrl;
    logic                     flush_unissued_instr_ctrl_id;
    logic                     flush_ctrl_if;
    logic                     flush_ctrl_id;
    logic                     flush_ctrl_ex;
    logic                     flush_tlb_ctrl_ex;
    logic                     fence_i_commit_controller;
    logic                     fence_commit_controller;
    logic                     sfence_vma_commit_controller;
    logic                     halt_ctrl;
    logic                     halt_debug_ctrl;
    logic                     halt_csr_ctrl;
    logic                     flush_dcache_ctrl_ex;
    logic                     flush_dcache_ack_ex_ctrl;
    // --------------
    // Debug <-> *
    // --------------
    logic [63:0]              pc_debug_pcgen;
    logic                     set_pc_debug;

    logic                     gpr_req_debug_issue;
    logic [4:0]               gpr_addr_debug_issue;
    logic                     gpr_we_debug_issue;
    logic [63:0]              gpr_wdata_debug_issue;
    logic [63:0]              gpr_rdata_debug_issue;

    logic                     csr_req_debug_csr;
    logic [11:0]              csr_addr_debug_csr;
    logic                     csr_we_debug_csr;
    logic [63:0]              csr_wdata_debug_csr;
    logic [63:0]              csr_rdata_debug_csr;
    // ----------------
    // ICache <-> *
    // ----------------
    logic                    flush_icache_ctrl_icache;
    logic                    bypass_icache_csr_icache;

    assign sec_lvl_o = priv_lvl;
    assign flush_dcache_ack_o = flush_dcache_ack_ex_ctrl;
    // --------------
    // Frontend
    // --------------
    frontend #(
        .BTB_ENTRIES         ( BTB_ENTRIES ),
        .BHT_ENTRIES         ( BHT_ENTRIES ),
        .RAS_DEPTH           ( RAS_DEPTH   )
    ) i_frontend (
        .flush_i             ( flush_ctrl_if                 ), // not entirely correct
        .flush_bp_i          ( 1'b0                          ),
        .flush_icache_i      ( flush_icache_ctrl_icache      ),
        .boot_addr_i         ( boot_addr_i                   ),
        .fetch_enable_i      ( fetch_enable                  ),
        .fetch_req_o         ( fetch_req_if_ex               ),
        .fetch_vaddr_o       ( fetch_vaddr_if_ex             ),
        .fetch_valid_i       ( fetch_valid_ex_if             ),
        .fetch_paddr_i       ( fetch_paddr_ex_if             ),
        .fetch_exception_i   ( fetch_ex_ex_if                ),
        .resolved_branch_i   ( resolved_branch               ),
        .pc_commit_i         ( pc_commit                     ),
        .set_pc_commit_i     ( set_pc_ctrl_pcgen             ),
        .epc_i               ( epc_commit_pcgen              ),
        .eret_i              ( eret                          ),
        .trap_vector_base_i  ( trap_vector_base_commit_pcgen ),
        .ex_valid_i          ( ex_commit.valid               ),
        .debug_pc_i          ( pc_debug_pcgen                ),
        .debug_set_pc_i      ( set_pc_debug                  ),
        .axi                 ( instr_if                      ),
        .l1_icache_miss_o    (                               ), // performance counters
        .fetch_entry_o       ( fetch_entry_if_id             ),
        .fetch_entry_valid_o ( fetch_valid_if_id             ),
        .fetch_ack_i         ( decode_ack_id_if              ),
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
    issue_stage #(
        .NR_ENTRIES                 ( NR_SB_ENTRIES                   ),
        .NR_WB_PORTS                ( NR_WB_PORTS                     )
    ) issue_stage_i (
        .flush_unissued_instr_i     ( flush_unissued_instr_ctrl_id    ),
        .flush_i                    ( flush_ctrl_id                   ),
        // Debug
        .debug_gpr_req_i            ( gpr_req_debug_issue             ),
        .debug_gpr_addr_i           ( gpr_addr_debug_issue            ),
        .debug_gpr_we_i             ( gpr_we_debug_issue              ),
        .debug_gpr_wdata_i          ( gpr_wdata_debug_issue           ),
        .debug_gpr_rdata_o          ( gpr_rdata_debug_issue           ),

        .decoded_instr_i            ( issue_entry_id_issue            ),
        .decoded_instr_valid_i      ( issue_entry_valid_id_issue      ),
        .is_ctrl_flow_i             ( is_ctrl_fow_id_issue            ),
        .decoded_instr_ack_o        ( issue_instr_issue_id            ),

        // Functional Units
        .fu_o                       ( fu_id_ex                        ),
        .operator_o                 ( operator_id_ex                  ),
        .operand_a_o                ( operand_a_id_ex                 ),
        .operand_b_o                ( operand_b_id_ex                 ),
        .imm_o                      ( imm_id_ex                       ),
        .trans_id_o                 ( trans_id_id_ex                  ),
        .pc_o                       ( pc_id_ex                        ),
        .is_compressed_instr_o      ( is_compressed_instr_id_ex       ),
        // ALU
        .alu_ready_i                ( alu_ready_ex_id                 ),
        .alu_valid_o                ( alu_valid_id_ex                 ),
        // Branches and Jumps
        .branch_ready_i             ( branch_ready_ex_id              ),
        .branch_valid_o             ( branch_valid_id_ex              ), // branch is valid
        .branch_predict_o           ( branch_predict_id_ex            ), // branch predict to ex
        .resolve_branch_i           ( resolve_branch_ex_id            ), // in order to resolve the branch
        // LSU
        .lsu_ready_i                ( lsu_ready_ex_id                 ),
        .lsu_valid_o                ( lsu_valid_id_ex                 ),
        // Multiplier
        .mult_ready_i               ( mult_ready_ex_id                ),
        .mult_valid_o               ( mult_valid_id_ex                ),
        // CSR
        .csr_ready_i                ( csr_ready_ex_id                 ),
        .csr_valid_o                ( csr_valid_id_ex                 ),

        .trans_id_i                 ( {alu_trans_id_ex_id,         lsu_trans_id_ex_id,  branch_trans_id_ex_id,    csr_trans_id_ex_id,         mult_trans_id_ex_id        }),
        .wbdata_i                   ( {alu_result_ex_id,           lsu_result_ex_id,    branch_result_ex_id,      csr_result_ex_id,           mult_result_ex_id          }),
        .ex_ex_i                    ( {{$bits(exception_t){1'b0}}, lsu_exception_ex_id, branch_exception_ex_id,   {$bits(exception_t){1'b0}}, {$bits(exception_t){1'b0}} }),
        .wb_valid_i                 ( {alu_valid_ex_id,            lsu_valid_ex_id,     branch_valid_ex_id,       csr_valid_ex_id,            mult_valid_ex_id           }),

        .waddr_i                    ( waddr_commit_id               ),
        .wdata_i                    ( wdata_commit_id               ),
        .we_i                       ( we_commit_id                  ),
        .we_fpr_i                   ( ), // TODO
        .commit_instr_o             ( commit_instr_id_commit        ),
        .commit_ack_i               ( commit_ack                    ),
        .*
    );

    // ---------
    // EX
    // ---------
    ex_stage #(
        .CACHE_START_ADDR ( CACHE_START_ADDR ),
        .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH   ( AXI_USER_WIDTH   )
    ) ex_stage_i (
        .flush_i                ( flush_ctrl_ex                          ),
        .fu_i                   ( fu_id_ex                               ),
        .operator_i             ( operator_id_ex                         ),
        .operand_a_i            ( operand_a_id_ex                        ),
        .operand_b_i            ( operand_b_id_ex                        ),
        .imm_i                  ( imm_id_ex                              ),
        .trans_id_i             ( trans_id_id_ex                         ),
        .pc_i                   ( pc_id_ex                               ),
        .is_compressed_instr_i  ( is_compressed_instr_id_ex              ),
        // ALU
        .alu_ready_o            ( alu_ready_ex_id                        ),
        .alu_valid_i            ( alu_valid_id_ex                        ),
        .alu_result_o           ( alu_result_ex_id                       ),
        .alu_trans_id_o         ( alu_trans_id_ex_id                     ),
        .alu_valid_o            ( alu_valid_ex_id                        ),
        .alu_branch_res_o       ( alu_branch_res_ex_id                   ),
        .alu_exception_o        (                                        ),
        // Branches and Jumps
        .branch_ready_o         ( branch_ready_ex_id                     ),
        .branch_valid_o         ( branch_valid_ex_id                     ),
        .branch_valid_i         ( branch_valid_id_ex                     ),
        .branch_trans_id_o      ( branch_trans_id_ex_id                  ),
        .branch_result_o        ( branch_result_ex_id                    ),
        .branch_exception_o     ( branch_exception_ex_id                 ),
        .branch_predict_i       ( branch_predict_id_ex                   ), // branch predict to ex
        .resolved_branch_o      ( resolved_branch                        ),
        .resolve_branch_o       ( resolve_branch_ex_id                   ),
        // LSU
        .lsu_ready_o            ( lsu_ready_ex_id                        ),
        .lsu_valid_i            ( lsu_valid_id_ex                        ),
        .lsu_result_o           ( lsu_result_ex_id                       ),
        .lsu_trans_id_o         ( lsu_trans_id_ex_id                     ),
        .lsu_valid_o            ( lsu_valid_ex_id                        ),
        .lsu_commit_i           ( lsu_commit_commit_ex                   ), // from commit
        .lsu_commit_ready_o     ( lsu_commit_ready_ex_commit             ), // to commit
        .lsu_exception_o        ( lsu_exception_ex_id                    ),
        .no_st_pending_o        ( no_st_pending_ex_commit                ),
        // CSR
        .csr_ready_o            ( csr_ready_ex_id                        ),
        .csr_valid_i            ( csr_valid_id_ex                        ),
        .csr_trans_id_o         ( csr_trans_id_ex_id                     ),
        .csr_result_o           ( csr_result_ex_id                       ),
        .csr_valid_o            ( csr_valid_ex_id                        ),
        .csr_addr_o             ( csr_addr_ex_csr                        ),
        .csr_commit_i           ( csr_commit_commit_ex                   ), // from commit
        // Performance counters
        .itlb_miss_o            ( itlb_miss_ex_perf                      ),
        .dtlb_miss_o            ( dtlb_miss_ex_perf                      ),
        .dcache_miss_o          ( dcache_miss_ex_perf                    ),
        // Memory Management
        .enable_translation_i   ( enable_translation_csr_ex              ), // from CSR
        .en_ld_st_translation_i ( en_ld_st_translation_csr_ex            ),
        .flush_tlb_i            ( flush_tlb_ctrl_ex                      ),

        .fetch_req_i            ( fetch_req_if_ex                        ),
        .fetch_valid_o          ( fetch_valid_ex_if                      ),
        .fetch_vaddr_i          ( fetch_vaddr_if_ex                      ),
        .fetch_paddr_o          ( fetch_paddr_ex_if                      ),
        .fetch_exception_o      ( fetch_ex_ex_if                         ), // fetch exception to IF
        .priv_lvl_i             ( priv_lvl                               ), // from CSR
        .ld_st_priv_lvl_i       ( ld_st_priv_lvl_csr_ex                  ), // from CSR
        .sum_i                  ( sum_csr_ex                             ), // from CSR
        .mxr_i                  ( mxr_csr_ex                             ), // from CSR
        .satp_ppn_i             ( satp_ppn_csr_ex                        ), // from CSR
        .asid_i                 ( asid_csr_ex                            ), // from CSR

        .mult_ready_o           ( mult_ready_ex_id                       ),
        .mult_valid_i           ( mult_valid_id_ex                       ),
        .mult_trans_id_o        ( mult_trans_id_ex_id                    ),
        .mult_result_o          ( mult_result_ex_id                      ),
        .mult_valid_o           ( mult_valid_ex_id                       ),

        .data_if                ( data_if                                ),
        .dcache_en_i            ( dcache_en_csr_nbdcache                 ),
        .flush_dcache_i         ( flush_dcache_ctrl_ex | flush_dcache_i  ),
        .flush_dcache_ack_o     ( flush_dcache_ack_ex_ctrl               ),

        .*
    );

    // ---------
    // Commit
    // ---------
    commit_stage commit_stage_i (
        .halt_i                 ( halt_ctrl                     ),
        .exception_o            ( ex_commit                     ),
        .commit_instr_i         ( commit_instr_id_commit        ),
        .commit_ack_o           ( commit_ack                    ),
        .no_st_pending_i        ( no_st_pending_ex_commit       ),
        .waddr_o                ( waddr_commit_id               ),
        .wdata_o                ( wdata_commit_id               ),
        .we_o                   ( we_commit_id                  ),
        .we_fpr_o               ( ), // write FPU reg, TODO
        .commit_lsu_o           ( lsu_commit_commit_ex          ),
        .commit_lsu_ready_i     ( lsu_commit_ready_ex_commit    ),
        .commit_csr_o           ( csr_commit_commit_ex          ),
        .pc_o                   ( pc_commit                     ),
        .csr_op_o               ( csr_op_commit_csr             ),
        .csr_wdata_o            ( csr_wdata_commit_csr          ),
        .csr_rdata_i            ( csr_rdata_csr_commit          ),
        .csr_write_fflags_o     ( csr_write_fflags_commit_cs    ),
        .csr_exception_i        ( csr_exception_csr_commit      ),
        .fence_i_o              ( fence_i_commit_controller     ),
        .fence_o                ( fence_commit_controller       ),
        .sfence_vma_o           ( sfence_vma_commit_controller  ),
        .*
    );

    // ---------
    // CSR
    // ---------
    csr_regfile #(
        .ASID_WIDTH             ( ASID_WIDTH                    )
    ) csr_regfile_i (
        .flush_o                ( flush_csr_ctrl                ),
        .halt_csr_o             ( halt_csr_ctrl                 ),
        .debug_csr_req_i        ( csr_req_debug_csr             ),
        .debug_csr_addr_i       ( csr_addr_debug_csr            ),
        .debug_csr_we_i         ( csr_we_debug_csr              ),
        .debug_csr_wdata_i      ( csr_wdata_debug_csr           ),
        .debug_csr_rdata_o      ( csr_rdata_debug_csr           ),
        .commit_ack_i           ( commit_ack                    ),
        .ex_i                   ( ex_commit                     ),
        .csr_op_i               ( csr_op_commit_csr             ),
        .csr_write_fflags_i     ( csr_write_fflags_commit_cs    ),
        .csr_addr_i             ( csr_addr_ex_csr               ),
        .csr_wdata_i            ( csr_wdata_commit_csr          ),
        .csr_rdata_o            ( csr_rdata_csr_commit          ),
        .pc_i                   ( pc_commit                     ),
        .csr_exception_o        ( csr_exception_csr_commit      ),
        .epc_o                  ( epc_commit_pcgen              ),
        .eret_o                 ( eret                          ),
        .fflags_o               ( ), // FPU flags out
        .frm_o                  ( ), // FPU rounding mode flags out TODO
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
        .dcache_en_o            ( dcache_en_csr_nbdcache        ),
        .icache_en_o            ( bypass_icache_csr_icache      ),
        .perf_addr_o            ( addr_csr_perf                 ),
        .perf_data_o            ( data_csr_perf                 ),
        .perf_data_i            ( data_perf_csr                 ),
        .perf_we_o              ( we_csr_perf                   ),
        .*
    );


    // ------------------------
    // Performance Counters
    // ------------------------
    perf_counters i_perf_counters (
        .addr_i            ( addr_csr_perf          ),
        .we_i              ( we_csr_perf            ),
        .data_i            ( data_csr_perf          ),
        .data_o            ( data_perf_csr          ),
        .commit_instr_i    ( commit_instr_id_commit ),
        .commit_ack_i      ( commit_ack             ),

        .l1_icache_miss_i  ( 1'b0                   ),
        .l1_dcache_miss_i  ( dcache_miss_ex_perf    ),
        .itlb_miss_i       ( itlb_miss_ex_perf      ),
        .dtlb_miss_i       ( dtlb_miss_ex_perf      ),

        .ex_i              ( ex_commit              ),
        .eret_i            ( eret                   ),
        .resolved_branch_i ( resolved_branch        ),
        .*
    );
    // ------------
    // Controller
    // ------------
    controller controller_i (
        // flush ports
        .flush_bp_o             ( flush_bp_ctrl_pcgen           ),
        .set_pc_commit_o        ( set_pc_ctrl_pcgen             ),
        .flush_unissued_instr_o ( flush_unissued_instr_ctrl_id  ),
        .flush_if_o             ( flush_ctrl_if                 ),
        .flush_id_o             ( flush_ctrl_id                 ),
        .flush_ex_o             ( flush_ctrl_ex                 ),
        .flush_tlb_o            ( flush_tlb_ctrl_ex             ),
        .flush_dcache_o         ( flush_dcache_ctrl_ex          ),
        .flush_dcache_ack_i     ( flush_dcache_ack_ex_ctrl      ),

        .halt_csr_i             ( halt_csr_ctrl                 ),
        .halt_debug_i           ( halt_debug_ctrl               ),
        .debug_set_pc_i         ( set_pc_debug                  ),
        .halt_o                 ( halt_ctrl                     ),
        // control ports
        .eret_i                 ( eret                          ),
        .ex_valid_i             ( ex_commit.valid               ),
        .flush_csr_i            ( flush_csr_ctrl                ),
        .resolved_branch_i      ( resolved_branch               ),
        .fence_i_i              ( fence_i_commit_controller     ),
        .fence_i                ( fence_commit_controller       ),
        .sfence_vma_i           ( sfence_vma_commit_controller  ),

        .flush_icache_o         ( flush_icache_ctrl_icache      ),
        .*
    );

    // ------------
    // Debug
    // ------------
    debug_unit debug_unit_i (
        .commit_instr_i    ( commit_instr_id_commit[0] ),
        .commit_ack_i      ( commit_ack[0]             ),
        .ex_i              ( ex_commit                 ),
        .halt_o            ( halt_debug_ctrl           ),
        .fetch_enable_i    ( fetch_enable              ),

        .debug_pc_o        ( pc_debug_pcgen            ),
        .debug_set_pc_o    ( set_pc_debug              ),

        .debug_gpr_req_o   ( gpr_req_debug_issue       ),
        .debug_gpr_addr_o  ( gpr_addr_debug_issue      ),
        .debug_gpr_we_o    ( gpr_we_debug_issue        ),
        .debug_gpr_wdata_o ( gpr_wdata_debug_issue     ),
        .debug_gpr_rdata_i ( gpr_rdata_debug_issue     ),

        .debug_csr_req_o   ( csr_req_debug_csr         ),
        .debug_csr_addr_o  ( csr_addr_debug_csr        ),
        .debug_csr_we_o    ( csr_we_debug_csr          ),
        .debug_csr_wdata_o ( csr_wdata_debug_csr       ),
        .debug_csr_rdata_i ( csr_rdata_debug_csr       ),
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
    assign tracer_if.issue_ack         = issue_stage_i.i_scoreboard.issue_ack_i;
    assign tracer_if.issue_sbe         = issue_stage_i.i_scoreboard.issue_instr_o;
    // write-back
    assign tracer_if.waddr             = waddr_commit_id;
    assign tracer_if.wdata             = wdata_commit_id;
    assign tracer_if.we                = we_commit_id;
    // commit
    assign tracer_if.commit_instr      = commit_instr_id_commit;
    assign tracer_if.commit_ack        = commit_ack;
    // branch predict
    assign tracer_if.resolve_branch    = resolved_branch;
    // address translation
    // stores
    assign tracer_if.st_valid          = ex_stage_i.lsu_i.i_store_unit.store_buffer_i.valid_i;
    assign tracer_if.st_paddr          = ex_stage_i.lsu_i.i_store_unit.store_buffer_i.paddr_i;
    // loads
    assign tracer_if.ld_valid          = ex_stage_i.lsu_i.i_load_unit.tag_valid_o;
    assign tracer_if.ld_kill           = ex_stage_i.lsu_i.i_load_unit.kill_req_o;
    assign tracer_if.ld_paddr          = ex_stage_i.lsu_i.i_load_unit.paddr_i;
    // exceptions
    assign tracer_if.exception         = commit_stage_i.exception_o;
    // assign current privilege level
    assign tracer_if.priv_lvl          = priv_lvl;

    instr_tracer instr_tracer_i (tracer_if, cluster_id_i, core_id_i);
    `endif
    `endif

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            fetch_enable <= 0;
        end else begin
            fetch_enable <= fetch_enable_i;
        end
    end

    `ifndef SYNTHESIS
    `ifndef verilator
    program instr_tracer
        (
            instruction_tracer_if tracer_if,
            input logic [5:0] cluster_id_i,
            input logic [3:0] core_id_i
        );

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
    // mock tracer for Verilator, to be used with spike-dasm
    `else

    string s;
    int f;
    logic [63:0] cycles;

    initial begin
        f = $fopen("trace_core_00_0.dasm", "w");
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            cycles <= 0;
        end else begin
            for (int i = 0; i < NR_COMMIT_PORTS; i++) begin
                if (commit_ack[i] && !commit_stage_i.exception_o) begin
                    $fwrite(f, "%d 0x%0h (0x%h) DASM(%h)\n", cycles, commit_instr_id_commit[i].pc, commit_instr_id_commit[i].ex.tval[31:0], commit_instr_id_commit[i].ex.tval[31:0]);
                end else if (commit_ack[i] && commit_instr_id_commit[i].ex.valid) begin
                    if (commit_instr_id_commit[i].ex.cause == 2) begin
                        $fwrite(f, "Exception Cause: Illegal Instructions, DASM(%h)\n", commit_instr_id_commit[i].ex.tval[31:0]);
                    end else begin
                        $fwrite(f, "Exception Cause: %5d\n", commit_instr_id_commit[i].ex.cause);
                    end
                end
            end
            cycles <= cycles + 1;
        end
    end

    final begin
        $fclose(f);
    end
    `endif
    `endif
endmodule // ariane

