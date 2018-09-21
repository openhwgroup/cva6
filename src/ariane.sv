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
`endif
`endif

module ariane #(
        parameter logic [63:0] CACHE_START_ADDR = 64'h8000_0000, // address on which to decide whether the request is cache-able or not
        parameter int unsigned AXI_ID_WIDTH     = 10,            // minimum 1
        parameter int unsigned AXI_USER_WIDTH   = 1              // minimum 1
    )(
        input  logic                           clk_i,
        input  logic                           rst_ni,
        // Core ID, Cluster ID and boot address are considered more or less static
        input  logic [63:0]                    boot_addr_i,  // reset boot address
        input  logic [ 3:0]                    core_id_i,    // core id in a multicore environment (reflected in a CSR)
        input  logic [ 5:0]                    cluster_id_i, // PULP specific if core is used in a clustered environment
        // Instruction memory interface
        AXI_BUS.Master                         instr_if,
        // Data memory interface
        AXI_BUS.Master                         data_if,      // data cache refill port
        AXI_BUS.Master                         bypass_if,    // bypass axi port (disabled cache or uncacheable access)
        // Interrupt inputs
        input  logic [1:0]                     irq_i,        // level sensitive IR lines, mip & sip (async)
        input  logic                           ipi_i,        // inter-processor interrupts (async)
        // Timer facilities
        input  logic                           time_irq_i,   // timer interrupt in (async)
        input  logic                           debug_req_i   // debug request (async)
    );

    // ------------------------------------------
    // Global Signals
    // Signals connecting more than one module
    // ------------------------------------------
    riscv::priv_lvl_t           priv_lvl;
    exception_t                 ex_commit; // exception from commit stage
    branchpredict_t             resolved_branch;
    logic [63:0]                pc_commit;
    logic                       eret;
    logic [NR_COMMIT_PORTS-1:0] commit_ack;

    // --------------
    // PCGEN <-> CSR
    // --------------
    logic [63:0]              trap_vector_base_commit_pcgen;
    logic [63:0]              epc_commit_pcgen;
    // --------------
    // IF <-> ID
    // --------------
    fetch_entry_t             fetch_entry_if_id;
    logic                     fetch_valid_if_id;
    logic                     decode_ack_id_if;

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
    logic                     amo_valid_commit;
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
    // CSR <-> *
    // --------------
    logic                     enable_translation_csr_ex;
    logic                     en_ld_st_translation_csr_ex;
    riscv::priv_lvl_t         ld_st_priv_lvl_csr_ex;
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
    logic                     icache_en_csr;
    logic                     debug_mode_csr_id;
    logic                     single_step_csr_commit;
    // ----------------------------
    // Performance Counters <-> *
    // ----------------------------
    logic [11:0]              addr_csr_perf;
    logic [63:0]              data_csr_perf, data_perf_csr;
    logic                     we_csr_perf;

    logic                     icache_flush_ctrl_cache;
    logic                     itlb_miss_ex_perf;
    logic                     dtlb_miss_ex_perf;
    logic                     dcache_miss_cache_perf;
    logic                     icache_miss_cache_perf;
    // --------------
    // CTRL <-> *
    // --------------
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
    logic                     halt_csr_ctrl;
    logic                     dcache_flush_ctrl_cache;
    logic                     dcache_flush_ack_cache_ctrl;
    logic                     set_debug_pc;

    icache_areq_i_t           icache_areq_ex_cache;
    icache_areq_o_t           icache_areq_cache_ex;
    icache_dreq_i_t           icache_dreq_if_cache;
    icache_dreq_o_t           icache_dreq_cache_if;

    amo_req_t                 amo_req;
    amo_resp_t                amo_resp;

    logic debug_req;
    // Disable debug during AMO commit
    assign debug_req = debug_req_i & ~amo_valid_commit;

    // ----------------
    // DCache <-> *
    // ----------------
    dcache_req_i_t [2:0]      dcache_req_ports_ex_cache;
    dcache_req_o_t [2:0]      dcache_req_ports_cache_ex;

    // --------------
    // Frontend
    // --------------
    frontend i_frontend (
        .flush_i             ( flush_ctrl_if                 ), // not entirely correct
        .flush_bp_i          ( 1'b0                          ),
        .boot_addr_i         ( boot_addr_i                   ),
        .icache_dreq_i       ( icache_dreq_cache_if          ),
        .icache_dreq_o       ( icache_dreq_if_cache          ),
        .resolved_branch_i   ( resolved_branch               ),
        .pc_commit_i         ( pc_commit                     ),
        .set_pc_commit_i     ( set_pc_ctrl_pcgen             ),
        .set_debug_pc_i      ( set_debug_pc                  ),
        .epc_i               ( epc_commit_pcgen              ),
        .eret_i              ( eret                          ),
        .trap_vector_base_i  ( trap_vector_base_commit_pcgen ),
        .ex_valid_i          ( ex_commit.valid               ),
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
        .debug_mode_i               ( debug_mode_csr_id               ),
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

        .commit_instr_o             ( commit_instr_id_commit        ),
        .commit_ack_i               ( commit_ack                    ),
        .*
    );

    // ---------
    // EX
    // ---------
    ex_stage ex_stage_i (
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
        .amo_valid_commit_i     ( amo_valid_commit                       ),
        .amo_req_o              ( amo_req                                ),
        .amo_resp_i             ( amo_resp                               ),
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
        // Memory Management
        .enable_translation_i   ( enable_translation_csr_ex              ), // from CSR
        .en_ld_st_translation_i ( en_ld_st_translation_csr_ex            ),
        .flush_tlb_i            ( flush_tlb_ctrl_ex                      ),
        .priv_lvl_i             ( priv_lvl                               ), // from CSR
        .ld_st_priv_lvl_i       ( ld_st_priv_lvl_csr_ex                  ), // from CSR
        .sum_i                  ( sum_csr_ex                             ), // from CSR
        .mxr_i                  ( mxr_csr_ex                             ), // from CSR
        .satp_ppn_i             ( satp_ppn_csr_ex                        ), // from CSR
        .asid_i                 ( asid_csr_ex                            ), // from CSR
        .icache_areq_i          ( icache_areq_cache_ex                   ),
        .icache_areq_o          ( icache_areq_ex_cache                   ),

        .mult_ready_o           ( mult_ready_ex_id                       ),
        .mult_valid_i           ( mult_valid_id_ex                       ),
        .mult_trans_id_o        ( mult_trans_id_ex_id                    ),
        .mult_result_o          ( mult_result_ex_id                      ),
        .mult_valid_o           ( mult_valid_ex_id                       ),
        // DCACHE interfaces
        .dcache_req_ports_i     ( dcache_req_ports_cache_ex              ),
        .dcache_req_ports_o     ( dcache_req_ports_ex_cache              ),
        .*
    );

    // ---------
    // Commit
    // ---------
    commit_stage commit_stage_i (
        .clk_i,
        .rst_ni,
        .halt_i                 ( halt_ctrl                     ),
        .flush_dcache_i         ( dcache_flush_ctrl_cache       ),
        .exception_o            ( ex_commit                     ),
        .debug_mode_i           ( debug_mode_csr_id             ),
        .debug_req_i            ( debug_req                     ),
        .single_step_i          ( single_step_csr_commit        ),
        .commit_instr_i         ( commit_instr_id_commit        ),
        .commit_ack_o           ( commit_ack                    ),
        .no_st_pending_i        ( no_st_pending_ex_commit       ),
        .waddr_o                ( waddr_commit_id               ),
        .wdata_o                ( wdata_commit_id               ),
        .we_o                   ( we_commit_id                  ),
        .commit_lsu_o           ( lsu_commit_commit_ex          ),
        .commit_lsu_ready_i     ( lsu_commit_ready_ex_commit    ),
        .amo_valid_commit_o     ( amo_valid_commit              ),
        .amo_resp_i             ( amo_resp                      ),
        .commit_csr_o           ( csr_commit_commit_ex          ),
        .pc_o                   ( pc_commit                     ),
        .csr_op_o               ( csr_op_commit_csr             ),
        .csr_wdata_o            ( csr_wdata_commit_csr          ),
        .csr_rdata_i            ( csr_rdata_csr_commit          ),
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
        .commit_instr_i         ( commit_instr_id_commit        ),
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
        .set_debug_pc_o         ( set_debug_pc                  ),
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
        .debug_mode_o           ( debug_mode_csr_id             ),
        .single_step_o          ( single_step_csr_commit        ),
        .dcache_en_o            ( dcache_en_csr_nbdcache        ),
        .icache_en_o            ( icache_en_csr                 ),
        .perf_addr_o            ( addr_csr_perf                 ),
        .perf_data_o            ( data_csr_perf                 ),
        .perf_data_i            ( data_perf_csr                 ),
        .perf_we_o              ( we_csr_perf                   ),
        .debug_req_i            ( debug_req                     ),
        .ipi_i,
        .irq_i,
        .time_irq_i,
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

        .l1_icache_miss_i  ( icache_miss_cache_perf ),
        .l1_dcache_miss_i  ( dcache_miss_cache_perf ),
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
        .set_pc_commit_o        ( set_pc_ctrl_pcgen             ),
        .flush_unissued_instr_o ( flush_unissued_instr_ctrl_id  ),
        .flush_if_o             ( flush_ctrl_if                 ),
        .flush_id_o             ( flush_ctrl_id                 ),
        .flush_ex_o             ( flush_ctrl_ex                 ),
        .flush_tlb_o            ( flush_tlb_ctrl_ex             ),
        .flush_dcache_o         ( dcache_flush_ctrl_cache       ),
        .flush_dcache_ack_i     ( dcache_flush_ack_cache_ctrl   ),

        .halt_csr_i             ( halt_csr_ctrl                 ),
        .halt_o                 ( halt_ctrl                     ),
        // control ports
        .eret_i                 ( eret                          ),
        .ex_valid_i             ( ex_commit.valid               ),
        .set_debug_pc_i         ( set_debug_pc                  ),
        .flush_csr_i            ( flush_csr_ctrl                ),
        .resolved_branch_i      ( resolved_branch               ),
        .fence_i_i              ( fence_i_commit_controller     ),
        .fence_i                ( fence_commit_controller       ),
        .sfence_vma_i           ( sfence_vma_commit_controller  ),

        .flush_icache_o         ( icache_flush_ctrl_cache       ),
        .*
    );

    // -------------------
    // Cache Subsystem
    // -------------------
    std_cache_subsystem #(
        .CACHE_START_ADDR      ( CACHE_START_ADDR                      )
    ) i_std_cache_subsystem (
        // to D$
        .clk_i                 ( clk_i                                 ),
        .rst_ni                ( rst_ni                                ),
        // I$
        .icache_en_i           ( icache_en_csr                         ),
        .icache_flush_i        ( icache_flush_ctrl_cache               ),
        .icache_miss_o         ( icache_miss_cache_perf                ),
        .icache_areq_i         ( icache_areq_ex_cache                  ),
        .icache_areq_o         ( icache_areq_cache_ex                  ),
        .icache_dreq_i         ( icache_dreq_if_cache                  ),
        .icache_dreq_o         ( icache_dreq_cache_if                  ),
        // D$
        .dcache_enable_i       ( dcache_en_csr_nbdcache                ),
        .dcache_flush_i        ( dcache_flush_ctrl_cache               ),
        .dcache_flush_ack_o    ( dcache_flush_ack_cache_ctrl           ),
        // to commit stage
        .amo_req_i             ( amo_req                               ),
        .amo_resp_o            ( amo_resp                              ),
        .dcache_miss_o         ( dcache_miss_cache_perf                ),
        // from PTW, Load Unit  and Store Unit
        .dcache_req_ports_i    ( dcache_req_ports_ex_cache             ),
        .dcache_req_ports_o    ( dcache_req_ports_cache_ex             ),
        // memory side
        .icache_data_if        ( instr_if                              ),
        .dcache_data_if        ( data_if                               ),
        .dcache_bypass_if      ( bypass_if                             )
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
    assign tracer_if.ld_valid          = ex_stage_i.lsu_i.i_load_unit.req_port_o.tag_valid;
    assign tracer_if.ld_kill           = ex_stage_i.lsu_i.i_load_unit.req_port_o.kill_req;
    assign tracer_if.ld_paddr          = ex_stage_i.lsu_i.i_load_unit.paddr_i;
    // exceptions
    assign tracer_if.exception         = commit_stage_i.exception_o;
    // assign current privilege level
    assign tracer_if.priv_lvl          = priv_lvl;
    assign tracer_if.debug_mode        = debug_mode_csr_id;
    instr_tracer instr_tracer_i (tracer_if, cluster_id_i, core_id_i);
    `endif
    `endif

    `ifndef SYNTHESIS
    `ifndef verilator
    program instr_tracer (
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
                if (commit_ack[i] && !commit_instr_id_commit[i].ex.valid) begin
                    $fwrite(f, "%d 0x%0h (0x%h) DASM(%h)\n", cycles, commit_instr_id_commit[i].pc, commit_instr_id_commit[i].ex.tval[31:0], commit_instr_id_commit[i].ex.tval[31:0]);
                end else if (commit_ack[i] && commit_instr_id_commit[i].ex.valid) begin
                    if (commit_instr_id_commit[i].ex.cause == 2) begin
                        $fwrite(f, "Exception Cause: Illegal Instructions, DASM(%h) PC=%h\n", commit_instr_id_commit[i].ex.tval[31:0], commit_instr_id_commit[i].pc);
                    end else begin
                        if (debug_mode_csr_id) begin
                            $fwrite(f, "%d 0x%0h (0x%h) DASM(%h)\n", cycles, commit_instr_id_commit[i].pc, commit_instr_id_commit[i].ex.tval[31:0], commit_instr_id_commit[i].ex.tval[31:0]);
                        end else begin
                            $fwrite(f, "Exception Cause: %5d, DASM(%h) PC=%h\n", commit_instr_id_commit[i].ex.cause, commit_instr_id_commit[i].ex.tval[31:0], commit_instr_id_commit[i].pc);
                        end
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

