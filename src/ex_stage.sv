
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
// Date: 19.04.2017
// Description: Instantiation of all functional units residing in the execute stage

import ariane_pkg::*;

module ex_stage #(
        parameter int          ASID_WIDTH       = 1
    ) (
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    input  logic                                   flush_i,

    input  fu_t                                    fu_i,
    input  fu_op                                   operator_i,
    input  logic [63:0]                            operand_a_i,
    input  logic [63:0]                            operand_b_i,
    input  logic [63:0]                            imm_i,
    input  logic [TRANS_ID_BITS-1:0]               trans_id_i,
    input  logic [63:0]                            pc_i,                  // PC of current instruction
    input  logic                                   is_compressed_instr_i, // we need to know if this was a compressed instruction
                                                                          // in order to calculate the next PC on a mis-predict
    // ALU 1
    output logic                                   alu_ready_o,           // FU is ready
    input  logic                                   alu_valid_i,           // Output is valid
    output logic                                   alu_valid_o,           // ALU result is valid
    output logic [63:0]                            alu_result_o,
    output logic [TRANS_ID_BITS-1:0]               alu_trans_id_o,        // ID of scoreboard entry at which to write back
    // Branches and Jumps
    output logic                                   branch_ready_o,
    input  logic                                   branch_valid_i,        // we are using the branch unit
    output logic                                   branch_valid_o,        // the calculated branch target is valid
    output logic [63:0]                            branch_result_o,       // branch target address out
    input  branchpredict_sbe_t                     branch_predict_i,      // branch prediction in
    output logic [TRANS_ID_BITS-1:0]               branch_trans_id_o,
    output exception_t                             branch_exception_o,    // branch unit detected an exception

    output branchpredict_t                         resolved_branch_o,     // the branch engine uses the write back from the ALU
    output logic                                   resolve_branch_o,      // to ID signaling that we resolved the branch
    // LSU
    output logic                                   lsu_ready_o,           // FU is ready
    input  logic                                   lsu_valid_i,           // Input is valid
    output logic                                   lsu_valid_o,           // Output is valid
    output logic [63:0]                            lsu_result_o,
    output logic [TRANS_ID_BITS-1:0]               lsu_trans_id_o,
    input  logic                                   lsu_commit_i,
    output logic                                   lsu_commit_ready_o,    // commit queue is ready to accept another commit request
    output exception_t                             lsu_exception_o,
    output logic                                   no_st_pending_o,
    // CSR
    output logic                                   csr_ready_o,
    input  logic                                   csr_valid_i,
    output logic [TRANS_ID_BITS-1:0]               csr_trans_id_o,
    output logic [63:0]                            csr_result_o,
    output logic                                   csr_valid_o,
    output logic [11:0]                            csr_addr_o,
    input  logic                                   csr_commit_i,
    // MULT
    output logic                                   mult_ready_o,      // FU is ready
    input  logic                                   mult_valid_i,      // Output is valid
    output logic [TRANS_ID_BITS-1:0]               mult_trans_id_o,
    output logic [63:0]                            mult_result_o,
    output logic                                   mult_valid_o,
    // FPU
    output logic                                   fpu_ready_o,      // FU is ready
    input  logic                                   fpu_valid_i,      // Output is valid
    input  logic [1:0]                             fpu_fmt_i,        // FP format
    input  logic [2:0]                             fpu_rm_i,         // FP rm
    input  logic [2:0]                             fpu_frm_i,        // FP frm csr
    output logic [TRANS_ID_BITS-1:0]               fpu_trans_id_o,
    output logic [63:0]                            fpu_result_o,
    output logic                                   fpu_valid_o,
    output exception_t                             fpu_exception_o,

    // Memory Management
    input  logic                                   enable_translation_i,
    input  logic                                   en_ld_st_translation_i,
    input  logic                                   flush_tlb_i,

    input  riscv::priv_lvl_t                       priv_lvl_i,
    input  riscv::priv_lvl_t                       ld_st_priv_lvl_i,
    input  logic                                   sum_i,
    input  logic                                   mxr_i,
    input  logic [43:0]                            satp_ppn_i,
    input  logic [ASID_WIDTH-1:0]                  asid_i,
    // icache translation requests
    input  icache_areq_o_t                         icache_areq_i,
    output icache_areq_i_t                         icache_areq_o,

    // interface to dcache
    input  dcache_req_o_t [2:0]                    dcache_req_ports_i,
    output dcache_req_i_t [2:0]                    dcache_req_ports_o,

    // Performance counters
    output logic                                   itlb_miss_o,
    output logic                                   dtlb_miss_o
);

    logic alu_branch_res; // branch comparison result

    // -----
    // ALU
    // -----
    alu alu_i (
        .result_o            ( alu_result_o                 ),
        .alu_branch_res_o    ( alu_branch_res               ),
        .*
    );

    // --------------------
    // Branch Engine
    // --------------------
    branch_unit branch_unit_i (
        .fu_valid_i          ( alu_valid_i || lsu_valid_i || csr_valid_i || mult_valid_i), // any functional unit is valid, check that there is no accidental mis-predict
        .branch_comp_res_i   ( alu_branch_res ),
        .*
    );

    // ----------------
    // Multiplication
    // ----------------
    mult i_mult (
        .result_o ( mult_result_o ),
        .*
    );

    // ----------------
    // FPU
    // ----------------
    generate
        if( FP_PRESENT ) begin : fpu_gen
            fpu_wrap fpu_i (
                .operand_c_i ( imm_i        ),
                .result_o    ( fpu_result_o ),
                .*
            );
        end else begin : no_fpu_gen
            assign fpu_ready_o     = '0;
            assign fpu_trans_id_o  = '0;
            assign fpu_result_o    = '0;
            assign fpu_valid_o     = '0;
            assign fpu_exception_o = '0;
        end
    endgenerate

    // ----------------
    // Load-Store Unit
    // ----------------
    lsu lsu_i (
        .commit_i           ( lsu_commit_i       ),
        .commit_ready_o     ( lsu_commit_ready_o ),
        .dcache_req_ports_i ( dcache_req_ports_i ),
        .dcache_req_ports_o ( dcache_req_ports_o ),
        .*
    );

    // -----
    // CSR
    // -----
    // CSR address buffer
    csr_buffer csr_buffer_i (
        .commit_i ( csr_commit_i  ),
        .*
    );


endmodule
